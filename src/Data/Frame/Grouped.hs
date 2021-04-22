module Data.Frame.Grouped where


data GroupedFrameKeys kcols =
    GroupedFrameKeys
        !(CombinedFactors Field kcols)


newtype GroupedFrame kdf kcols df cols =
    GroupedFrame
        (ZoomedFrame
            (GroupedFrameKeys kdf kcols)
            df
            cols)


instance IsFrame df => IsFrame (GroupedFrame k df) where
    frameLength (GroupedFrame zdf) = frameLength zdf

    type Column (GroupedFrame k df) = Column df

    data Eval (GroupedFrame k df) =
        GroupedEval (Eval (ZoomedFrame (FactorizedSeries k) df))

    withFrame prj = GroupedEval (withFrame (prj . GroupedFrame))
    getRowIndex = GroupedEval getRowIndex

    runEval (GroupedFrame zdf) (GroupedEval e) = runEval zdf e


withKey :: (Int -> k -> a) -> Eval (GroupedFrame k df) cols
withKey f = GroupedEval \ !fs ->
    let !ixfs = elemAt (indexSeries fs)
    in  (\i -> f i (ixfs i)) <$> getRowIndex


instance HasColumnAt df cols i => HasColumnAt (GroupedFrame k) cols i where
    findColumn proxy (GroupedFrame zdf) = findColumn proxy zdf
