module Data.Frame.Display where

import Type.Errors

import Data.Frame.Kind


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


printFrameType :: forall df cols.
    DelayError (PrettyPrintFrameType df cols)
    => df cols
    -> df cols
printFrameType = id

