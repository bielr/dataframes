module Data.Frame.Impl.ColVectors where

import Control.Lens (Iso, coerced)
import Control.Rowwise

import Data.Frame.Kind
import Data.Frame.Internal.ColVector
import Data.Heterogeneous.HSmallArray (HSmallArray)


type Column :: FieldK -> Type
newtype Column col = Column (ColVector (FieldType col))


colVector :: Iso (Column (s :> a)) (Column (s :> b)) (ColVector a) (ColVector b)
colVector = coerced


type Frame :: FrameK
newtype Frame cols = Frame (HSmallArray Column cols)


materializeCol :: forall s a cols. Rowwise (Frame cols) a -> Column (s :> a)
materializeCol =
