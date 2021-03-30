{-# language AllowAmbiguousTypes #-}
{-# language StrictData #-}
{-# language UndecidableInstances #-}
module Data.Frame.Internal.Column where

import GHC.TypeLits (KnownSymbol)

import Data.Coerce

import Control.Lens qualified as L
import Control.Lens.Indexed (Indexable)
import Control.Lens.LazyTraversal
import Control.Lens.Type
import Control.Monad.Primitive (PrimMonad, PrimState)

import Data.Vector.Generic.Lens (vectorTraverse)
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM

import Data.Vinyl.TypeLevel (Fst, Snd)

import Data.Indexer
import Data.Frame.Field
import Data.Frame.Internal.ColVector
import Data.Frame.Internal.Repr
import Data.Frame.Kind

import Data.Vinyl.Extra.TypeLevel.Constraints (All)


type ColType :: FieldK -> Constraint

class
    ( col ~ '(Fst col, Snd col)
    , KnownSymbol (Fst col)
    , KnownVectorMode (VectorModeOf (Snd col))
    , VG.Vector (VectorTypeOf (Snd col)) (Snd col)
    , VG.Vector (VectorTypeOf (Snd col)) (Field col)
    )
    => ColType col

instance
    ( col ~ '(Fst col, Snd col)
    , KnownSymbol (Fst col)
    , KnownVectorMode (VectorModeOf (Snd col))
    , VG.Vector (VectorTypeOf (Snd col)) (Snd col)
    , VG.Vector (VectorTypeOf (Snd col)) (Field col)
    )
    => ColType col


type ColTypes :: FieldsK -> Constraint
type ColTypes cols = All ColType cols


type Col :: Repr -> FieldK -> Type

data Col rep col where
    ColGen :: Indexer   (Field col) -> Col 'Idx col
    ColVec :: ColVector (Field col) -> Col 'Vec col


type ColRepF :: Repr -> Type -> Type

type family ColRepF rep = f | f -> rep where
    ColRepF 'Idx = Indexer
    ColRepF 'Vec = ColVector


type instance L.Index (Col rep col) = Int
type instance L.IxValue (Col rep col) = Field col


instance When (rep == 'Vec) (ColType col) => L.Ixed (Col rep col) where
    ix i f = \case
        ColVec v -> ColVec <$> L.ix i f v
        ColGen g -> ColGen <$> L.ix i f g
    {-# inline ix #-}


-- internal, should not be exposed to ensure data frame consistency
generateCol :: forall rep col.
    ( KnownRepr rep
    , When (rep == 'Vec) (ColType col)
    )
    => Indexer (Snd col)
    -> Col rep col
generateCol =
    case sRepr @rep of
      SIdx -> coerce ColGen
      SVec -> coerce (ColVec . copyIndexer)
{-# inline generateCol #-}


emptyCol :: forall rep col.
    ( KnownRepr rep
    , When (rep == 'Vec) (ColType col)
    )
    => Col rep col
emptyCol = generateCol mempty
{-# inline emptyCol #-}


appendCols ::
    When (rep == 'Vec) (ColType col)
    => Col rep col
    -> Col rep col
    -> Col rep col
appendCols (ColGen g1) (ColGen g2) = ColGen (g1 <> g2)
appendCols (ColVec v1) (ColVec v2) = ColVec (v1 VG.++ v2)
{-# inline appendCols #-}


concatCols :: forall rep col.
    ( KnownRepr rep
    , When (rep == 'Vec) (ColType col)
    )
    => [Col rep col]
    -> Col rep col
concatCols =
    case sRepr @rep of
      SIdx -> \cols -> ColGen $ concatIndexersN (length cols) [g | ColGen g <- cols]
      SVec -> \cols -> ColVec $ VG.concat                     [v | ColVec v <- cols]
{-# inline concatCols #-}


indexCol :: When (rep == 'Vec) (ColType col) => Col rep col -> Col 'Idx col
indexCol = \case
    ColGen g -> ColGen g
    ColVec v -> ColGen (indexVector v)
{-# inline indexCol #-}


forceCol :: ColType col => Col rep col -> Col 'Vec col
forceCol = \case
    ColGen g -> ColVec (copyIndexer g)
    ColVec v -> ColVec (VG.force v)
{-# inline forceCol #-}


fromCol :: Col rep col -> ColRepF rep (Field col)
fromCol = \case
    ColGen g -> g
    ColVec v -> v
{-# inline fromCol #-}


-- internal, should not be exposed to ensure data frame consistency
toCol :: forall rep col. KnownRepr rep => ColRepF rep (Field col) -> Col rep col
toCol =
    case sRepr @rep of
      SIdx -> ColGen
      SVec -> ColVec
{-# inline toCol #-}


-- internal, should not be exposed to ensure data frame consistency
colRepF ::
    KnownRepr rep'
    => Iso (Col rep col) (Col rep' col') (ColRepF rep (Field col)) (ColRepF rep' (Field col'))
colRepF = L.iso fromCol toCol
{-# inline colRepF #-}


type HasFields ::
    (FieldK -> Type)
    -> (Type -> Type -> Type)
    -> (Type -> Type -> Type)
    -> (Type -> Type)
    -> FieldK
    -> FieldK
    -> Constraint

class HasFields colF p q f col col' | colF p -> q where
    fields :: Optical p q f (colF col) (colF col') (Field col) (Field col')


instance p ~ q => HasFields Field p q f col col' where
    -- fields :: Equality (Field col) (Field col') (Field col) (Field col')
    fields = id
    {-# inline fields #-}


instance
    ( Indexable Int p
    , q ~ (->)
    , Applicative f
    , ColType col
    , ColType col'
    )
    => HasFields (Col 'Vec) p q f col col' where

    -- fields :: IndexedTraversal Int (Col 'Vec col) (Col 'Vec col') (Field col) (Field col')
    fields f (ColVec v) = ColVec <$> vectorTraverse f v
    {-# inline fields #-}


instance
    ( Indexable Int p
    , q ~ (->)
    , Applicative f
    , DistributiveFoldable f
    )
    => HasFields (Col 'Idx) p q f col col' where

    -- fields :: IndexedLazyTraversal Int (Col 'Idx col) (Col 'Idx col') (Field col) (Field col')
    fields f (ColGen g) = ColGen <$> ifoldMapped f g
    {-# inline fields #-}


colFields :: forall col col' rep p f.
    ( When (rep == 'Idx) (DistributiveFoldable f)
    , When (rep == 'Vec) (ColType col, ColType col')
    , KnownRepr rep
    , Indexable Int p
    , Applicative f
    )
    => Optical p (->) f (Col rep col) (Col rep col') (Field col) (Field col')
colFields =
    case sRepr @rep of
      SIdx -> fields
      SVec -> fields
{-# inline colFields #-}


type MCol :: Type -> FieldK -> Type

data MCol s col where
    ColMVec :: ColType col => ColMVector s (Field col) -> MCol s col


unsafeNewMCol :: (PrimMonad m, ColType col) => Int -> m (MCol (PrimState m) col)
unsafeNewMCol n = ColMVec <$> VGM.unsafeNew n
{-# inline unsafeNewMCol #-}


unsafeFreezeMCol :: PrimMonad m => MCol (PrimState m) col -> m (Col 'Vec col)
unsafeFreezeMCol (ColMVec mv) = ColVec <$> VG.unsafeFreeze mv
{-# inline unsafeFreezeMCol #-}
