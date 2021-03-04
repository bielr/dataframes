module Data.Frame.Internal.Repr where


data Repr  = Vec | Idx

data SRepr (rep :: Repr) where
    SVec :: SRepr 'Vec
    SIdx :: SRepr 'Idx

class KnownRepr rep where sRepr :: SRepr rep
instance KnownRepr 'Vec where sRepr = SVec
instance KnownRepr 'Idx where sRepr = SIdx


data Major = Rows | Cols

data SMajor (by :: Major) where
    SRows :: SMajor 'Rows
    SCols :: SMajor 'Cols

class KnownMajor by where sMajor :: SMajor by
instance KnownMajor 'Rows where sMajor = SRows
instance KnownMajor 'Cols where sMajor = SCols
