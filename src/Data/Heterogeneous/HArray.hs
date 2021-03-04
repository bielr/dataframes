module Data.Heterogeneous.HArray where


--instance HMonoid ARec where
--    hempty = ARec (A.array (0,-1) [])
--    /*# inline hempty #*/

--    happend (ARec as) (ARec bs) =
--      let
--        (0, u1) = A.bounds as
--        (0, u2) = A.bounds bs
--        u3 = u1+1 + u2+1 - 1
--      in
--        ARec $ A.listArray (0, u3) (A.elems as ++ A.elems bs)
--    /*# inline happend #*/

--    hcons fa (ARec afas) =
--        let
--          (0, u) = A.bounds afas
--        in
--          ARec (A.listArray (0, u+1) (unsafeCoerce fa : A.elems afas))
--    /*# inline hcons #*/


--instance
--    ( ReplaceSubseq ss ss' rs rs' is
--    , NatToInt (RLength ss)
--    , NatToInt (RLength rs)
--    , NatToInt (RLength rs')
--    , IndexWitnesses (RImage ss rs)
--    )
--    => HSubseqI ARec ss ss' rs rs' is where

--    hsubseqC = L.lens Vy.rcast $ \(ARec ars) (ARec ass') ->
--        let
--          replace :: Int -> [Int] -> [Any] -> [Any] -> [Any]
--          replace !_ _  rs []  = rs
--          replace !_ _  [] ss' = ss'
--          replace !_ [] rs ss' = ss' ++ rs

--          replace !i jjs@(j : js) (r : rs) s'ss'@(s' : ss')
--            | i == j    = s' : replace (i+1) js rs ss'
--            | otherwise = r : replace (i+1) jjs rs s'ss'

--          ars' = A.listArray (0, natToInt @(RLength rs') - 1) $
--                  replace 0 (indexWitnesses @is) (A.elems ars) (A.elems ass')
--        in
--            ARec ars'
--    {-# inlinable hsubseqC #-}

--    hsubseqSplitC Refl = L.iso
--        (\(ARec ars) ->
--            let
--              split :: Int -> [Any] -> [Int] -> ([Any], [Any])
--              split !_ rs [] = ([], rs)

--              split !i (r : rs) jjs@(j : js)
--                | i == j    = case split (i+1) rs js  of (!ss, !rs') -> (r : ss, rs')
--                | otherwise = case split (i+1) rs jjs of (!ss, !rs') -> (ss, r : rs')

--              split !_ [] (_:_) = error "hsubseqSplitC @ARec: split: the impossible happened"
--            in
--              case split 0 (A.elems ars) (indexWitnesses @is) of
--                (ss, rs') -> (ARec $ A.listArray (0, natToInt @(RLength ss) - 1) ss,
--                              ARec $ A.listArray (0, natToInt @(RLength rs') - 1) rs'))
--        (\(ARec ass, ARec ars') ->
--          let
--            merge :: Int -> [Int] -> [Any] -> [Any] -> [Any]
--            merge !_ [] [] rs' = rs'
--            merge !_ _  ss []  = ss

--            merge !i jjs@(j : js) sss@(s : ss) rrs'@(r : rs')
--              | i == j    = s : merge (i+1) js ss rrs'
--              | otherwise = r : merge (i+1) jjs sss rs'

--            merge !_ [] (_:_) _ = error "hsubseqSplitC @ARec: merge: the impossible happened"
--            merge !_ (_:_) [] _ = error "hsubseqSplitC @ARec: merge: the impossible happened"
--          in
--            ARec $ A.listArray (0, natToInt @(RLength rs) - 1) $
--              merge 0 (indexWitnesses @is) (A.elems ass) (A.elems ars'))
--    {-# inlinable hsubseqSplitC #-}
