{-# language MagicHash #-}
{-# language DeriveGeneric #-}
{-# language Strict #-}
module Data.Frame.Display
  ( debugFrameType
  , ShowOptions(..)
  , defaultShowOptions
  , showFrameWith
  , showFrame
  , printFrameWith
  , printFrame
  ) where

import GHC.Exts (proxy#)
import GHC.Generics (Generic)

import Control.DeepSeq (NFData, force)
import Control.Lens
import Data.Char (isPrint, isSpace)
import Data.Foldable (foldl', toList)
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy
import Data.Vector qualified as VB
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Typeable (Typeable, typeRep)
import Type.Errors

import Data.Functor.Boilerplate
import Data.Frame.Class hiding (col)
import Data.Frame.Field
import Data.Frame.Kind
import Data.Heterogeneous.TypeLevel
import Data.Heterogeneous.Class.HFunctor
import Data.Heterogeneous.Class.HFoldable
import Data.Heterogeneous.Constraints
import Data.Indexer


type PrettyPrintField :: FieldK -> ErrorMessage
type family PrettyPrintField col where
    PrettyPrintField (s :> a) = 'Text ", " ':<>: 'ShowType (s :> a)


type PrettyPrintFields :: FieldsK -> ErrorMessage
type family PrettyPrintFields cols where
    PrettyPrintFields '[]           = 'Text ""
    PrettyPrintFields (col ': cols) =
        PrettyPrintField col
        ':$$: 'Text ""
            ':<>: PrettyPrintFields cols


type PrettyPrintFrameType :: FrameK -> FieldsK -> ErrorMessage
type PrettyPrintFrameType df cols =
    'Text "At this point, the type of the data frame is "
    ':$$: 'ShowType df
        ':<>: 'Text " '["
    ':$$: 'Text "    "
        ':<>: PrettyPrintFields cols
        ':<>: 'Text "]"


debugFrameType :: forall df cols.
    DelayError (PrettyPrintFrameType df cols)
    => df cols
    -> df cols
debugFrameType = id


data ShowOptions = ShowOptions
    { maxFrameWidth      :: Int
    , cellMinWidth       :: Int
    , cellMaxWidth       :: Int
    , cellMinHeight      :: Int
    , cellMaxHeight      :: Int
    , showType           :: Bool
    , showTitleSeparator :: Bool
    , columnSeparator    :: Text
    }


data TextCell = TextLine {-# unpack #-} Text | TextLines (NonEmpty Text)
    deriving stock Generic

instance NFData TextCell


textCell :: Text -> TextCell
textCell t =
    cellLines # replaceEmpty (map sanitize (Text.lines t))
  where
    replaceEmpty [] = Text.empty :| []
    replaceEmpty (l:ls) = l :| ls

    sanitize = Text.map sanitizeChar
    sanitizeChar c
      | isSpace c = ' '
      | isPrint c = c
      | otherwise = '�'


cellLines :: Iso' TextCell (NonEmpty Text)
cellLines = iso toNE fromNE
  where
    toNE (TextLine l)   = l :| []
    toNE (TextLines ls) = ls

    fromNE (l :| []) = TextLine l
    fromNE ls        = TextLines ls


whitespaceCache :: [Text]
whitespaceCache = map (\n -> Text.replicate n (Text.pack " ")) [0..]


emptyCell :: TextCell
emptyCell = TextLine Text.empty


vappendTextCell :: TextCell -> TextCell -> TextCell
vappendTextCell c c' =
    c & cellLines <>~ c'^.cellLines


happendTextCell :: TextCell -> TextCell -> TextCell
happendTextCell c =
    cellLines %~ NonEmpty.zipWith (<>) (c^.cellLines)


cellWidth :: TextCell -> Int
cellWidth = maximum1Of (cellLines . folded . to Text.length)


cellHeight :: TextCell -> Int
cellHeight = lengthOf (cellLines.folded)


clampCellWidth :: Int -> TextCell -> TextCell
clampCellWidth maxW = cellLines.mapped %~ clampLine
  where
    clampLine l =
        case Text.compareLength l maxW of
            LT -> l
            EQ -> l
            GT
              | maxW >= 2 -> Text.take (maxW-1) l <> Text.pack "…"
              | otherwise -> Text.take maxW l


clampCellHeight :: Int -> TextCell -> TextCell
clampCellHeight maxH cell =
    case cell of
        TextLine _ -> cell
        TextLines (l :| ls)
          | cellHeight cell <= maxH -> cell
          | maxH > 1                -> mark $ TextLines (l :| take (maxH-1) ls)
          | otherwise               -> mark (TextLine l)
  where
    mark :: TextCell -> TextCell
    mark = cellLines.last1 <>~ Text.pack "…"


justifyCellWidth :: Int -> TextCell -> TextCell
justifyCellWidth w = cellLines.mapped %~ Text.justifyRight w ' '


type FormattedColumnF :: (Type -> Type) -> Type
data FormattedColumnF f = FormattedColumn
    { formattedTitle :: Simplified f TextCell
    , formattedValues :: VB.Vector (Simplified f TextCell)
    , columnWidth :: Simplified f Int
    }


type FormattedColumn :: Type
type FormattedColumn = FormattedColumnF Identity


justifyColumn :: ShowOptions -> TextCell -> VB.Vector TextCell -> FormattedColumn
justifyColumn opts hdr cells =
    let
        w = cellMinWidth opts `max` VB.foldl' max (cellWidth hdr) (VB.map cellWidth cells)

        jhdr = justifyCellWidth w hdr
        jcells = VB.map (justifyCellWidth w) cells
    in
        FormattedColumn jhdr jcells w


justifyCellHeight :: Int -> Int -> TextCell -> TextCell
justifyCellHeight minH w =
    cellLines.tail1 %~ \ls ->
        let h = 1 + length ls
        in
            if h < minH then
                let whitespace = whitespaceCache !! w
                in  ls ++ replicate (minH - h) whitespace
            else
                ls
  where
    tail1 :: Lens' (NonEmpty a) [a]
    tail1 f (a :| as) = fmap (a :|) (f as)


formatColumn :: forall col df.
    ( IsFrame df
    , KnownField df col
    , Show (FieldType col)
    , Typeable (FieldType col)
    )
    => ShowOptions
    -> Column df col
    -> FormattedColumn
formatColumn opts col =
    let (w, h) = (cellMaxWidth opts, cellMaxHeight opts)

        toTextCell = clampCellWidth w . clampCellHeight h . textCell

        name = Text.pack (fieldName @col proxy#)

        ~ty   = Text.pack "<"
                <> Text.pack (show (typeRep @_ @(FieldType col) Proxy))
                <> Text.pack ">"

        header
            | showType opts = toTextCell name `vappendTextCell` toTextCell ty
            | otherwise     = toTextCell name

        values = copyIndexer $
            fmap (toTextCell . Text.pack . show . getField) $
                view colFields col
    in
        justifyColumn opts header values


formatColumns :: forall cols hf df.
    ( IsFrame df
    , All (KnownField df) cols
    , AllE Show FieldTypeExp cols
    , AllE Typeable FieldTypeExp cols
    , HFoldable hf cols
    )
    => ShowOptions
    -> hf (Column df) cols
    -> [FormattedColumn]
formatColumns opts =
    hitoListWith $
        iconstrained @(KnownField df) @cols $
            iconstrained @(ComposeExpC Show FieldTypeExp) @cols $
                constrained @(ComposeExpC Typeable FieldTypeExp) @cols $ \col ->
                    formatColumn opts col


splitByMaxWidthMaybe ::
    ShowOptions
    -> VB.Vector FormattedColumn
    -> Maybe (VB.Vector FormattedColumn, VB.Vector FormattedColumn)
splitByMaxWidthMaybe opts cols
    | VB.null cols = Nothing
    | otherwise    =
        let accWidths = VB.postscanl' (+) 0 $ VB.map (+sepLen) $ VB.map columnWidth cols
            nfitCols = VB.length $ VB.takeWhile (<= maxFrameWidth opts + sepLen) accWidths
        in
            Just (VB.splitAt (max nfitCols 1) cols)
  where
    sepLen = Text.length (columnSeparator opts)


colGroupsByMaxWidth ::
    ShowOptions
    -> VB.Vector FormattedColumn
    -> VB.Vector (VB.Vector FormattedColumn)
colGroupsByMaxWidth = VB.unfoldr . splitByMaxWidthMaybe


justifyRow :: [Int] -> [TextCell] -> [TextCell]
justifyRow ws row =
     let minH = foldl' max 1 (map cellHeight row)
     in
         zipWith (justifyCellHeight minH) ws row


emptyColumnF :: FormattedColumnF []
emptyColumnF = FormattedColumn [] VB.empty []


prependColumnF :: FormattedColumn -> FormattedColumnF [] -> FormattedColumnF []
prependColumnF col1 col2 = FormattedColumn
    { formattedTitle = formattedTitle col1 : formattedTitle col2
    , formattedValues =
        if VB.null (formattedValues col2) then
            VB.map pure (formattedValues col1)
        else if VB.null (formattedValues col1) then
            formattedValues col2
        else
            VB.zipWith (:) (formattedValues col1) (formattedValues col2)
    , columnWidth = columnWidth col1 : columnWidth col2
    }


joinColumnF :: ShowOptions -> FormattedColumnF [] -> FormattedColumn
joinColumnF opts cols = FormattedColumn
    { formattedTitle =
        force $ concatRow $ justifyRow ws (formattedTitle cols)
    , formattedValues =
        force $ VB.map (concatRow . justifyRow ws) (formattedValues cols)
    , columnWidth =
        foldl' (+) 0 $ intersperse (Text.length sep) ws
    }
  where
    ws :: [Int]
    ws = columnWidth cols

    sep :: Text
    sep = columnSeparator opts

    appendCells :: TextCell -> TextCell -> TextCell
    appendCells c c' = (c & cellLines.mapped <>~ sep) `happendTextCell` c'

    concatRow :: [TextCell] -> TextCell
    concatRow []     = emptyCell
    concatRow (c:cs) = foldl' appendCells c cs


hconcatColumns :: ShowOptions -> VB.Vector FormattedColumn -> FormattedColumn
hconcatColumns opts =
    joinColumnF opts . VB.foldr prependColumnF emptyColumnF


columnToLines :: ShowOptions -> FormattedColumn -> [Text]
columnToLines opts col =
    toList (formattedTitle col^.cellLines)
    ++
    titleSep
    ++
    concatMap (toList . view cellLines) (VB.toList (formattedValues col))
  where
    titleSep
      | showTitleSeparator opts = [Text.replicate (columnWidth col) (Text.pack "-")]
      | otherwise               = []


defaultShowOptions :: ShowOptions
defaultShowOptions = ShowOptions
    { maxFrameWidth      = 120
    , cellMinWidth       = 1
    , cellMaxWidth       = 10
    , cellMinHeight      = 1
    , cellMaxHeight      = 2
    , showTitleSeparator = True
    , showType           = True
    , columnSeparator    = Text.pack " | "
    }


showFrameWith :: forall cols df hf.
    ( AllE Show FieldTypeExp cols
    , AllE Typeable FieldTypeExp cols
    , All (KnownField df) cols
    , KnownLength cols

    , Columnar df hf cols
    , HFunctor hf cols
    , HFoldable hf cols
    )
    => ShowOptions
    -> df cols
    -> Text
showFrameWith opts df = df
    & toCols
    & VB.fromList . formatColumns opts
    & colGroupsByMaxWidth opts
    & VB.map (Text.intercalate nl . columnToLines opts . hconcatColumns opts)
    & Text.unlines . VB.toList
  where
    nl = Text.pack "\n"


showFrame :: forall cols df hf.
    ( AllE Show FieldTypeExp cols
    , AllE Typeable FieldTypeExp cols
    , All (KnownField df) cols
    , KnownLength cols

    , Columnar df hf cols
    , HFunctor hf cols
    , HFoldable hf cols
    )
    => df cols
    -> Text
showFrame = showFrameWith defaultShowOptions


printFrameWith :: forall cols df hf.
    ( AllE Show FieldTypeExp cols
    , AllE Typeable FieldTypeExp cols
    , All (KnownField df) cols
    , KnownLength cols

    , Columnar df hf cols
    , HFunctor hf cols
    , HFoldable hf cols
    )
    => ShowOptions
    -> df cols
    -> IO ()
printFrameWith opts = Text.putStrLn . showFrameWith opts


printFrame :: forall cols df hf.
    ( AllE Show FieldTypeExp cols
    , AllE Typeable FieldTypeExp cols
    , All (KnownField df) cols
    , KnownLength cols

    , Columnar df hf cols
    , HFunctor hf cols
    , HFoldable hf cols
    )
    => df cols
    -> IO ()
printFrame = Text.putStrLn . showFrame
