import Data.List

%default total

-- Stuff on permutations. Compiles (painfully slowly) under Idris 1.3.0.
--
-- I've made extensive use of a trick Pete Vanderbilt showed me: when pattern
-- matching on a term whose type contains a subterm on which pattern matching is
-- not possible, substitute a superfluous-looking variable for the subterm and
-- add a parameter that equates the variable to the subterm. See, for example,
-- permSwap', permSwapAfter', permDrop', permInsertAnywhere' permDropAnywhere'.


||| Permutation
data Perm: List a -> List a -> Type where
  PermNil: Perm [] []
  PermInsert: Perm r1 (l2 ++ r2) -> Perm (x :: r1) (l2 ++ x :: r2)

-- Perm is reflexive -----------------------------------------------------------

||| Perm is reflexive
permRefl: Perm as as
permRefl {as = []} = PermNil
permRefl {as = _ :: xs} = PermInsert {l2 = []} (permRefl {as = xs})

-- Cons vs nil -----------------------------------------------------------------

||| This is also in the prelude under the uninspiring name "lemma_val_not_nil"
consIsntNil: _ :: _ = [] -> Void
consIsntNil Refl impossible

-- Fun facts about Elem --------------------------------------------------------

||| An element x is in a list if there are elements l to the left of x and
||| elements r to the right
elemBetween: Elem x (l ++ x :: r)
elemBetween {l = []} = Here
elemBetween {l = y :: ys} = There (elemBetween {l = ys})

||| If x is an element of xs, then we can construct elements l to the left of x
||| and elements r to the right
elemBetweenWhat:
    {a: Type} -> {x: a} -> {xs: List a} ->
    Elem x xs ->
    (l: List a ** r: List a ** xs = l ++ x :: r)
elemBetweenWhat {xs = x :: ys} Here = ([] ** ys ** Refl)
elemBetweenWhat {xs = y :: ys} (There later) =
  let (ysl ** ysr ** ysEq) = elemBetweenWhat later
  in rewrite ysEq in (y :: ysl ** ysr ** Refl)

||| If x is an element of a list, and you insert another element y into the
||| list, x is still an element of the result
stillElemAfterInsert: Elem x (l ++ r) -> Elem x (l ++ y :: r)
stillElemAfterInsert {l = []} lm = There lm
stillElemAfterInsert {x = x} {l = x :: _} Here = Here
stillElemAfterInsert {x = x} {l = y :: ys} {r = r} {y = y'} (There later) =
  let afterY': Elem x (ys ++ y' :: r) = stillElemAfterInsert later
  in There afterY'

-- Equal conses ----------------------------------------------------------------

||| Two nonempty lists that are equal have equal heads
equalHeads: {xs, ys: List a}  -> x :: xs = y :: ys -> x = y
equalHeads Refl = Refl

||| Two nonempty lists that are equal have equal tails
equalTails: {xs, ys: List a} -> _ :: xs = _ :: ys -> xs = ys
equalTails Refl = Refl

||| If parts are equal, conses are equal
equalConses: {xs, ys: List a} -> x = y -> xs = ys -> x :: xs = y :: ys
equalConses Refl Refl = Refl

-- Concatenated lists ----------------------------------------------------------

||| Cons can be rephrased as prepending a one-element list
consVsAppend: (xs: List a) -> [x] ++ xs = x :: xs
consVsAppend xs = Refl

||| A list l prepended to a nonempty list r can be rewritten to associate the
||| first element of the nonempty list with initial list
consEqAppend: (xs: List a) -> xs ++ y :: ys = (xs ++ [y]) ++ ys
consEqAppend [] = Refl
consEqAppend {y} {ys} (z :: zs) =
  let recur = consEqAppend {y = y} {ys = ys} zs
  in  cong {f = (z ::)} recur

||| If you prepend a list l to a list r and the result is r, then l was empty
prependListUnchanged: {l: List a} -> l ++ r = r -> l = []
prependListUnchanged {l = []} Refl = Refl
prependListUnchanged {l = (_ :: _)} {r = []} Refl impossible
prependListUnchanged {l = (x :: xs)} {r = (y :: ys)} eq =
  let eqTls: (xs ++ y :: ys = ys) = equalTails eq
      eqTls' = trans (sym (consEqAppend {y = y} {ys = ys} xs)) eqTls
      recur = prependListUnchanged {l = xs ++ [y]} eqTls'
  in case xs of
       [] => void (consIsntNil recur)
       (x :: ys) => void (consIsntNil recur)

||| Any empty concatenation is a concatenation of empties
emptyConcat: as ++ bs = [] -> (as = [],bs = [])
emptyConcat {as = []} {bs = []} Refl = (Refl, Refl)
emptyConcat {as = []} {bs = (_ :: _)} Refl impossible
emptyConcat {as = _ :: _} Refl impossible

||| Prepending a nonempty list to a list r never results in r unchanged
prependingChangesList: x :: xs ++ r = r -> Void
prependingChangesList {x} {xs} eq =
  let ohNo: (x :: xs = []) = prependListUnchanged eq
  in void (consIsntNil ohNo)

||| If prepending prefixes to the same list results in equal lists, the prefixes
||| were equal
equalPrefixes: {l1, l2: List a} -> l1 ++ r = l2 ++ r -> l1 = l2
equalPrefixes {l1} {l2} {r = []} eq =
  rewrite sym (appendNilRightNeutral l2) in
  rewrite sym (appendNilRightNeutral l1) in eq
equalPrefixes {l1 = []} {l2 = []} {r = (z :: zs)} eq = Refl
equalPrefixes {l1 = []} {l2 = (x :: xs)} {r = (z :: zs)} eq =
  void (prependingChangesList (sym eq))
equalPrefixes {l1 = (x :: xs)} {l2 = []} {r = (z :: zs)} eq =
    void (prependingChangesList eq)
equalPrefixes {l1 = (x :: xs)} {l2 = (y :: ys)} {r = (z :: zs)} eq =
  let eqHds = equalHeads eq
      eqTls: (xs ++ z :: zs = ys ++ z :: zs) = equalTails eq
      recur = equalPrefixes {l1 = xs} {l2 = ys} eqTls
  in case eqHds of
       Refl => case recur of
         Refl => Refl

||| If two pairs of concatenated lists are equal, then the first part of the
||| first list can be the same length as, shorter, or longer than the first
||| part of the second, and we can rephrase the list with a middle piece that
||| can be joined with the shorter pieces to make the longer pieces
equalConcats3:
  {l1, r1, l2, r2: List a} ->
  l1 ++ r1 = l2 ++ r2 ->
  Either
    (l1 = l2, r1 = r2)
    (Either
      (m: a ** ms: List a ** (l2 = l1 ++ m :: ms, r1 = m :: ms ++ r2))
      (m: a ** ms: List a ** (l1 = l2 ++ m :: ms, r2 = m :: ms ++ r1)))
equalConcats3 {l1 = []} {l2 = []} eq = Left (Refl,eq)
equalConcats3 {l1 = []} {l2 = y :: ys} eq = Right (Left (y ** ys ** (Refl,eq)))
equalConcats3 {l1 = x :: xs} {l2 = []} eq =
  Right (Right (x ** xs ** (Refl,sym eq)))
equalConcats3 {l1 = x :: xs} {l2 = y :: ys} eq =
  let xEqY: (x = y) = equalHeads eq
  in  case (equalConcats3 (equalTails eq)) of
        Left (Refl,Refl) => Left (equalPrefixes eq,Refl)
        Right (Left (m ** ms ** (l2Longer,r1Longer))) =>
          Right (Left (m ** ms ** (equalConses (sym xEqY) l2Longer,r1Longer)))
        Right (Right (m ** ms ** (l1Longer,r2Longer))) =>
          Right (Right (m ** ms ** (equalConses xEqY l1Longer,r2Longer)))
      
-- Lists and lengths -----------------------------------------------------------

||| If a list has an element inserted anywhere into it, it's not empty
insertedNotEmpty: (length (as ++ x :: bs) = 0) -> Void
insertedNotEmpty {as = []} Refl impossible
insertedNotEmpty {as = _ :: _} Refl impossible

-- Stuff about Perms and Lists -------------------------------------------------

||| If x is in xs and xs is a permutation of ys, then x is in ys
elemInAllPerms: Elem x xs -> Perm xs ys -> Elem x ys
elemInAllPerms Here (PermInsert _) = elemBetween
elemInAllPerms {x} (There later) (PermInsert {r1} {l2} {r2} permNoY) =
  let xInL2R2: Elem x (l2 ++ r2) = elemInAllPerms later permNoY
  in stillElemAfterInsert xInL2R2
  
||| Two permutations have the same length
permLength: Perm xs ys -> length xs = length ys
permLength {xs = []} {ys = []} PermNil = Refl
permLength {xs = x :: r1} {ys = l2 ++ x :: r2} (PermInsert permNoX) =
  let recur: (length r1 = length (l2 ++ r2)) = permLength permNoX
      sRecur: (S (length r1) = S (length (l2 ++ r2))) = cong recur
      l2R2AppLen: (S (length (l2 ++ r2)) = S (length l2 + length r2)) =
        cong (lengthAppend l2 r2)
      sHead: (S (length l2 + length r2) = length l2 + S (length r2)) =
        plusSuccRightSucc (length l2) (length r2)
      xSplitLen: (length l2 + S (length r2) = length (l2 ++ x :: r2)) =
        sym (lengthAppend l2 (x :: r2))
  in  trans (trans (trans sRecur l2R2AppLen) sHead) xSplitLen
  
||| If you append the same list to two permuted lists, you get a permutation
permBeforeSame: Perm as bs -> Perm (as ++ l) (bs ++ l)
permBeforeSame {as = []} {bs = []} {l} PermNil = permRefl
permBeforeSame {as = x :: r1} {bs = l2 ++ x :: r2} {l} (PermInsert permNoX) =
  let recur: Perm (r1 ++ l) ((l2 ++ r2) ++ l) = permBeforeSame permNoX
      reassoc: Perm (r1 ++ l) (l2 ++ r2 ++ l) =
        rewrite appendAssociative l2 r2 l in recur
      insert: Perm (x :: r1 ++ l) (l2 ++ x :: r2 ++ l) = PermInsert reassoc
  in  rewrite (sym (appendAssociative l2 (x :: r2) l)) in insert

||| If stick two permuted lists between the same pair of lists, you get a
||| permutation
permMiddleSame: Perm as bs -> Perm (l ++ as ++ r) (l ++ bs ++ r)
permMiddleSame {l = []} permAsBs = permBeforeSame permAsBs
permMiddleSame {as} {bs} {l = y :: ys} {r} permAsBs =
  let recur: Perm (ys ++ as ++ r) (ys ++ bs ++ r) = permMiddleSame permAsBs
  in  PermInsert {l2 = []} recur

||| If a list is a permutation of a concatenation, you can reverse the order of
||| the concatenation and still have a permutation
permSwap: Perm l (xs ++ ys) -> Perm l (ys ++ xs)
permSwap perm = permSwap' perm Refl
  where
  permSwap': Perm l v -> v = as ++ bs -> Perm l (bs ++ as)
  permSwap' {l = []} PermNil eq =
    case emptyConcat (sym eq) of
      (Refl,Refl) => PermNil
  permSwap' {l = x :: xs} {as = []} (PermInsert {l2} {r2} permNoX) eq =
    case eq of
      Refl =>
        rewrite appendNilRightNeutral (l2 ++ x :: r2) in PermInsert permNoX
  permSwap' {l = x :: xs} {as = y :: ys} {bs}
      (PermInsert {l2 = []} {r2} permNoX) eq =
    case eq of
      Refl =>
        let permNoX': Perm xs (ys ++ bs) = permNoX
            recur: Perm xs (bs ++ ys) = permSwap' permNoX' Refl
        in  PermInsert recur
  permSwap' {l = x :: xs} {as = y :: ys} {bs}
      (PermInsert {l2 = z :: zs} {r2} permNoX) eq =
    case equalConcats3 eq of
      Left (Refl,Refl) =>
        let recur: Perm xs (r2 ++ y :: ys) = permSwap' permNoX Refl
        in  PermInsert {l2 = []} recur
      Right (Left (m ** ms ** (Refl,Refl))) =>
        let reassoc1: (ms ++ bs ++ y :: zs = (ms ++ bs) ++ y :: zs) =
              appendAssociative _ _ _
            recur1: Perm xs (ms ++ bs ++ y :: zs) =
              rewrite reassoc1 in permSwap' permNoX Refl
            recur2: Perm xs ((bs ++ y :: zs) ++ ms) =
              permSwap' recur1 Refl
            permWithM: Perm (m :: xs) ((bs ++ y :: zs) ++ m :: ms) =
              PermInsert recur2
            reassoc2: (bs ++ y :: zs ++ m :: ms = (bs ++ y :: zs) ++ m :: ms) =
              appendAssociative bs (y :: zs) (m :: ms)
        in  rewrite reassoc2 in permWithM
      Right (Right (m ** ms ** (Refl,Refl))) =>
        let reassoc1: (y :: ys ++ m :: ms ++ r2 = (y :: ys ++ m :: ms) ++ r2) =
              appendAssociative (y :: ys) (m :: ms) r2
            permNoXReassoc: Perm xs (y :: ys ++ m :: ms ++ r2) =
              rewrite reassoc1 in permNoX
            recur1: Perm xs ((m :: ms ++ r2) ++ y :: ys) =
              permSwap' permNoXReassoc Refl
            reassoc2: (m :: ms ++ r2 ++ y :: ys = (m :: ms ++ r2) ++ y :: ys) =
              appendAssociative (m :: ms) r2 (y :: ys)
            recur2: Perm xs (m :: ms ++ r2 ++ y :: ys) =
              rewrite reassoc2 in recur1
            permX: Perm (x :: xs) (m :: ms ++ x :: (r2 ++ y :: ys)) =
              PermInsert {l2 = m :: ms} recur2
            reassoc3: (m :: ms ++ x :: r2 ++ y :: ys =
                (m :: ms ++ x :: r2) ++ y :: ys) =
              appendAssociative (m :: ms) (x :: r2) (y :: ys)
        in  rewrite sym reassoc3 in permX

||| If a list is a permutation of a concatenation of three lists, you can
||| reverse the order of the last two and still have a permutation
permSwapAfter: Perm l (as ++ bs ++ cs) -> Perm l (as ++ cs ++ bs)
permSwapAfter perm =
  permSwapAfter' perm Refl
  where
  permSwapAfter': Perm l v -> v = aa ++ bb ++ cc -> Perm l (aa ++ cc ++ bb)
  permSwapAfter' {l} {aa = []} {bb} {cc} perm Refl =
    permSwap {l = l} {xs = bb} {ys = cc} perm
  permSwapAfter' {l} {aa} {bb = []} {cc} perm Refl =
    let reassoc: (aa ++ cc ++ [] = (aa ++ cc) ++ []) =
          appendAssociative aa cc []
        aacc: ((aa ++ cc) ++ [] = aa ++ cc) = appendNilRightNeutral (aa ++ cc)
    in  rewrite trans reassoc aacc in perm
  permSwapAfter' {l} {aa} {bb} {cc = []} perm Refl =
    let reassoc: (aa ++ bb ++ [] = (aa ++ bb) ++ []) =
          appendAssociative aa bb []
        aabb: ((aa ++ bb) ++ [] = aa ++ bb) = appendNilRightNeutral (aa ++ bb)
    in  rewrite sym (trans reassoc aabb) in perm
  permSwapAfter' {l = []} {aa = a :: as} {bb = b :: bs} {cc = c :: cs} perm eq =
    case perm of
      PermNil => case eq of
        Refl impossible
  permSwapAfter' {l = y :: ys} {aa = a :: as} {bb = b :: bs} {cc = c :: cs}
      (PermInsert {l2} {r2} permNoX) eq =
    case equalConcats3 eq of
      Left (Refl,Refl) =>
        let recur: Perm ys (a :: as ++ c :: cs ++ bs) =
              permSwapAfter' permNoX Refl
            reassoc1: (a :: as ++ c :: cs ++ bs = (a :: as ++ c :: cs) ++ bs) =
              appendAssociative (a :: as) (c :: cs) bs
            recur1: Perm ys ((a :: as ++ c :: cs) ++ bs) =
              rewrite sym reassoc1 in recur
            insert: Perm (b :: ys) ((a :: as ++ c :: cs) ++ b :: bs) =
              PermInsert {l2 = a :: as ++ c :: cs} {r2 = bs} recur1
            reassoc2: (a :: as ++ c :: cs ++ b :: bs =
                       (a :: as ++ c :: cs) ++ b :: bs) =
              appendAssociative (a :: as) (c :: cs) (b :: bs)
        in  rewrite reassoc2 in insert
      Right (Left (m ** ms ** (eqL,Refl))) =>
        case equalConcats3 {l1 = []} {r1 = a :: as} eqL of
          Left (Refl,Refl) =>
            let recur: Perm ys (as ++ c :: cs ++ b :: bs) =
                  permSwapAfter' {aa = as} {bb = b :: bs} {cc = c :: cs}
                    permNoX Refl
            in  PermInsert {l2 = []} {r2 = as ++ c :: cs ++ b :: bs} recur
          Right (Left (m1 ** ms1 ** (Refl,Refl))) =>
            let reassoc1: ((m1 :: ms1) ++ ms ++ b :: bs ++ c :: cs =
                           ((m1 :: ms1) ++ ms) ++ b :: bs ++ c :: cs) =
                  appendAssociative (m1 :: ms1) ms (b :: bs ++ c :: cs)
                perm1: Perm ys (((m1 :: ms1) ++ ms) ++ b :: bs ++ c :: cs) =
                  rewrite sym reassoc1 in permNoX
                recur: Perm ys (((m1 :: ms1) ++ ms) ++ c :: cs ++ b :: bs) =
                  permSwapAfter'
                    {aa = (m1 :: ms1) ++ ms} {bb = b :: bs} {cc = c :: cs}
                    perm1 Refl
                reassoc2:
                    (((m1 :: ms1) ++ ms ++ c :: cs ++ b :: bs) =
                      (((m1 :: ms1) ++ ms) ++ c :: cs ++ b :: bs)) =
                  appendAssociative (m1 :: ms1) ms (c :: cs ++ b :: bs)
                perm2: Perm ys ((m1 :: ms1) ++ ms ++ c :: cs ++ b :: bs) =
                  rewrite reassoc2 in recur
                insert:
                   Perm
                     (m :: ys) ((m1 :: ms1) ++ m :: ms ++ c :: cs ++ b :: bs) =
                  PermInsert {l2 = m1 :: ms1} {r2 = ms ++ c :: cs ++ b :: bs}
                    perm2
                reassoc3:
                    (((m1 :: ms1) ++ m :: ms ++ c :: cs ++ b :: bs) =
                      ((m1 :: ms1 ++ m :: ms) ++ c :: cs ++ b :: bs)) =
                  appendAssociative (m1 :: ms1) (m :: ms) (c :: cs ++ b :: bs)
            in  rewrite sym reassoc3 in insert
          Right (Right (m1 ** ms1 ** (eqL1,eqR1))) =>
            case l2 of
              [] => case eqL1 of
                Refl impossible
              _ :: _ => case eqL1 of
                Refl impossible
      Right (Right (m ** ms ** (Refl,eqR))) =>
        case equalConcats3 {l1 = b :: bs} {l2 = m :: ms} eqR of
          Left (Refl,Refl) =>
            let reassoc1:
                    (a :: as ++ b :: bs ++ cs = (a :: as ++ b :: bs) ++ cs) =
                  appendAssociative (a :: as) (b :: bs) cs
                perm1: Perm ys (a :: as ++ b :: bs ++ cs) =
                  rewrite reassoc1 in permNoX
                recur: Perm ys (a :: as ++ cs ++ b :: bs) =
                  permSwapAfter' {aa = a :: as} {bb = b :: bs} perm1 Refl
            in  PermInsert {l2 = a :: as} {r2 = cs ++ b :: bs} recur
          Right (Left (m1 ** ms1 ** (Refl,Refl))) =>
            let reassoc1: (a :: as ++ (b :: bs ++ m1 :: ms1) ++ r2 =
                            (a :: as ++ (b :: bs ++ m1 :: ms1)) ++ r2) =
                  appendAssociative (a :: as) (b :: bs ++ m1 :: ms1) r2
                reassoc2: ((b :: bs ++ m1 :: ms1 ++ r2) =
                            (b :: bs ++ m1 :: ms1) ++ r2) =
                  appendAssociative (b :: bs) (m1 :: ms1) r2
                perm1: Perm ys (a :: as ++ (b :: bs ++ m1 :: ms1) ++ r2) =
                  rewrite reassoc1 in permNoX
                perm2: Perm ys (a :: as ++ b :: bs ++ m1 :: ms1 ++ r2) =
                  rewrite reassoc2 in perm1
                recur: Perm ys (a :: as ++ (m1 :: ms1 ++ r2) ++ b :: bs) =
                  permSwapAfter' {aa = a :: as} {bb = b :: bs} perm2 Refl
                reassoc3: (m1 :: ms1 ++ r2 ++ b :: bs =
                            (m1 :: ms1 ++ r2) ++ b :: bs) =
                  appendAssociative (m1 :: ms1) r2 (b :: bs)
                recur1: Perm ys (a :: as ++ m1 :: ms1 ++ r2 ++ b :: bs) =
                  rewrite reassoc3 in recur
                reassoc4: (a :: as ++ m1 :: ms1 ++ r2 ++ b :: bs =
                            (a :: as ++ m1 :: ms1) ++ r2 ++ b :: bs) =
                  appendAssociative (a :: as) (m1 :: ms1) (r2 ++ b :: bs)
                recur2: Perm ys ((a :: as ++ m1 :: ms1) ++ r2 ++ b :: bs) =
                  rewrite sym reassoc4 in recur1
                insert:
                   Perm
                     (y :: ys) ((a :: as ++ m1 :: ms1) ++ y :: r2 ++ b :: bs) =
                  PermInsert {l2 = a :: as ++ m1 :: ms1} {r2 = r2 ++ b :: bs}
                    recur2
                reassoc5: (a :: as ++ m1 :: ms1 ++ y :: r2 ++ b :: bs =
                            (a :: as ++ m1 :: ms1) ++ y :: r2 ++ b :: bs) =
                  appendAssociative (a :: as) (m1 :: ms1) (y :: r2 ++ b :: bs)
                insert1: 
                   Perm (y :: ys) (a :: as ++ m1 :: ms1 ++ y :: r2 ++ b :: bs) =
                  rewrite reassoc5 in insert
                reassoc6: (m1 :: ms1 ++ y:: r2 ++ b :: bs =
                            (m1 :: ms1 ++ y :: r2) ++ b :: bs) =
                  appendAssociative (m1 :: ms1) (y :: r2) (b :: bs)
            in  rewrite sym reassoc6 in insert1
          Right (Right (m1 ** ms1 ** (Refl,Refl))) =>
            let reassoc1: (a :: as ++ b :: ms ++ ms1 ++ c :: cs =
                            (a :: as ++ b :: ms) ++ ms1 ++ c :: cs) =
                  appendAssociative (a :: as) (b :: ms) (ms1 ++ c :: cs)
                perm1: Perm ys (a :: as ++ b :: ms ++ ms1 ++ c :: cs) =
                  rewrite reassoc1 in permNoX
                recur1: Perm ys (a :: as ++ (ms1 ++ c :: cs) ++ b :: ms) =
                  permSwapAfter' {aa = a :: as} {bb = b :: ms} perm1 Refl
                reassoc2: (ms1 ++ c :: cs ++ b :: ms =
                            (ms1 ++ c :: cs) ++ b :: ms) =
                  appendAssociative ms1 (c :: cs) (b :: ms)
                recur11: Perm ys (a :: as ++ ms1 ++ c :: cs ++ b :: ms) =
                  rewrite reassoc2 in recur1
                recur2: Perm ys (a :: as ++ (c :: cs ++ b :: ms) ++ ms1) =
                   permSwapAfter' {aa = a :: as} {bb = ms1} recur11 Refl
                reassoc3: (a :: as ++ (c :: cs ++ b :: ms) ++ ms1 =
                            (a :: as ++ (c :: cs ++ b :: ms)) ++ ms1) =
                  appendAssociative (a :: as) (c :: cs ++ b :: ms) ms1
                recur21: Perm ys ((a :: as ++ (c :: cs ++ b :: ms)) ++ ms1) =
                  rewrite sym reassoc3 in recur2
                insert:
                    Perm (m1 :: ys)
                      ((a :: as ++ (c :: cs ++ b :: ms)) ++ m1 :: ms1) =
                  PermInsert {l2 = a :: as ++ (c :: cs ++ b :: ms)} {r2 = ms1}
                    recur21
                reassoc4: (a :: as ++ (c :: cs ++ b :: ms) ++ m1 :: ms1 =
                            (a :: as ++ (c :: cs ++ b :: ms)) ++ m1 :: ms1) =
                  appendAssociative (a :: as) (c :: cs ++ b :: ms) (m1 :: ms1)
                reassoc5: (c :: cs ++ b :: ms ++ m1 :: ms1 =
                            (c :: cs ++ b :: ms) ++ m1 :: ms1) =
                  appendAssociative (c :: cs) (b :: ms) (m1 :: ms1)
            in  rewrite reassoc5 in rewrite reassoc4 in insert

||| If a list is a permutation of four lists, you can swap the two middle lists
||| and still have a permutation
permSwapMiddle: Perm l (as ++ bs ++ cs ++ ds) -> Perm l (as ++ cs ++ bs ++ ds)
permSwapMiddle {l} {as} {bs} {cs} {ds} perm =
  let perm1: Perm l (as ++ (cs ++ ds) ++ bs) = permSwapAfter perm
      reassoc1: (cs ++ ds ++ bs = (cs ++ ds) ++ bs) = appendAssociative cs ds bs
      perm2: Perm l (as ++ cs ++ ds ++ bs) = rewrite reassoc1 in perm1
      reassoc2: (as ++ cs ++ ds ++ bs = (as ++ cs) ++ ds ++ bs) =
        appendAssociative as cs (ds ++ bs)
      perm3: Perm l ((as ++ cs) ++ ds ++ bs) = rewrite sym reassoc2 in perm2
      perm4: Perm l ((as ++ cs) ++ bs ++ ds) = permSwapAfter perm3
      reassoc3: (as ++ cs ++ bs ++ ds = (as ++ cs) ++ bs ++ ds) =
        appendAssociative as cs (bs ++ ds)
  in  rewrite reassoc3 in perm4

||| You can undo PermInsert
permDrop: Perm (x :: r1) (l2 ++ x :: r2) -> Perm r1 (l2 ++ r2)
permDrop permX =
  permDrop' permX Refl
  where
  permDrop': Perm (x :: r1) v -> v = l2 ++ x :: r2 -> Perm r1 (l2 ++ r2)
  permDrop' {x = x} {r1 = r1} {l2 = l2} {r2 = r2}
      (PermInsert {l2 = l3} {r2 = r3} permNoX) eq =
    case equalConcats3 eq of
      Left (Refl,Refl) =>
        permNoX
      Right (Left (m ** ms ** (Refl,Refl))) =>
        let perm: Perm r1 (l3 ++ m :: ms ++ r2) =
              permSwapMiddle {as = l3} {bs = ms} {cs = [m]} {ds = r2} permNoX
            reassoc: (l3 ++ m :: ms ++ r2 = (l3 ++ m :: ms) ++ r2) =
              appendAssociative l3 (m :: ms) r2
        in  rewrite sym reassoc in perm
      Right (Right (m ** ms ** (Refl,Refl))) =>
        let reassoc: (l2 ++ m :: ms ++ r3 = (l2 ++ m :: ms) ++ r3) =
              appendAssociative l2 (m :: ms) r3
            perm: Perm r1 (l2 ++ m :: ms ++ r3) = rewrite reassoc in permNoX
        in  permSwapMiddle {as = l2} {bs = [m]} {cs = ms} {ds = r3} perm
      
||| The type of PermInsert says you can insert an element at the head of the
||| left list, but actually you can insert it anywhere
permInsertAnywhere:
  Perm (l1 ++ r1) (l2 ++ r2) ->
  Perm (l1 ++ x :: r1) (l2 ++ x :: r2)
permInsertAnywhere perm =
  permInsertAnywhere' perm Refl Refl
  where
  permInsertAnywhere':
    Perm vl vr -> vl = l1 ++ r1 -> vr = l2 ++ r2 ->
      Perm (l1 ++ x :: r1) (l2 ++ x :: r2)
  permInsertAnywhere' PermNil eqL eqR =
    case (emptyConcat (sym eqL),emptyConcat (sym eqR)) of
      ((Refl,Refl),(Refl,Refl)) => permRefl
  permInsertAnywhere' {l1 = []} {r1} {l2} {r2} permNoX Refl Refl =
    PermInsert {r1 = r1} {l2 = l2} {r2 = r2} permNoX
  permInsertAnywhere' {l1 = y :: ys} {r1} {l2} {r2} {x}
      (PermInsert {r1 = r3} {l2 = l4} {r2 = r4} perm) eqL eqR =
    case eqL of
      Refl => case equalConcats3 eqR of
        Left (Refl,Refl) =>
          let recur: Perm (ys ++ x :: r1) (l2 ++ x :: r4) =
                permInsertAnywhere' perm Refl Refl
              reassoc1: (l2 ++ [x] ++ r4 = (l2 ++ [x]) ++  r4) =
                appendAssociative l2 [x] r4
              perm1: Perm (ys ++ x :: r1) ((l2 ++ [x]) ++ r4) =
                rewrite sym reassoc1 in recur
              insert: Perm (y :: ys ++ x :: r1) ((l2 ++ [x]) ++ y :: r4) =
                PermInsert perm1
              reassoc2: (l2 ++ x :: y :: r4 = (l2 ++ [x]) ++ y :: r4) =
                appendAssociative l2 [x] (y :: r4)
          in  rewrite reassoc2 in insert
        Right (Left (m ** ms ** (Refl,Refl))) =>
          let reassoc1: (l4 ++ ms ++ r2 = (l4 ++ ms) ++ r2) =
                appendAssociative l4 ms r2
              perm1: Perm (ys ++ r1) ((l4 ++ ms) ++ r2) =
                rewrite sym reassoc1 in perm
              recur: Perm (ys ++ x :: r1) ((l4 ++ ms) ++ x :: r2) =
                permInsertAnywhere' perm1 Refl Refl
              reassoc2: (l4 ++ ms ++ x :: r2 = (l4 ++ ms) ++ x :: r2) =
                appendAssociative l4 ms (x :: r2)
              perm2: Perm (ys ++ x :: r1) (l4 ++ ms ++ x :: r2) =
                rewrite reassoc2 in recur
              insert: Perm (m :: ys ++ x :: r1) (l4 ++ m :: ms ++ x :: r2) =
                PermInsert perm2
              reassoc3:
                 (l4 ++ m :: ms ++ x :: r2 = (l4 ++ m :: ms) ++ x :: r2) =
                appendAssociative l4 (m :: ms) (x :: r2)
          in  rewrite sym reassoc3 in insert
        Right (Right (m ** ms ** (Refl,Refl))) =>
          let reassoc1: (l2 ++ m :: ms ++ r4 = (l2 ++ m :: ms) ++ r4) =
                appendAssociative l2 (m :: ms) r4
              perm1: Perm (ys ++ r1) (l2 ++ m :: ms ++ r4) =
                rewrite reassoc1 in perm
              recur: Perm (ys ++ x :: r1) (l2 ++ x :: m :: ms ++ r4) =
                permInsertAnywhere' perm1 Refl Refl
              reassoc2:
                  (l2 ++ x :: m :: ms ++ r4 = (l2 ++ x :: m :: ms) ++ r4) =
                appendAssociative l2 (x :: m :: ms) r4
              recur1: Perm (ys ++ x :: r1) ((l2 ++ x :: m :: ms) ++ r4) =
                rewrite sym reassoc2 in recur
              insert:
                  Perm (y :: ys ++ x :: r1) ((l2 ++ x :: m :: ms) ++ y :: r4) =
                PermInsert recur1
              reassoc3:
                  (l2 ++ x :: m :: ms ++ y :: r4 =
                    (l2 ++ x :: m :: ms) ++ y :: r4) =
                appendAssociative l2 (x :: m :: ms) (y :: r4)
          in  rewrite reassoc3 in insert

-- Perm is symmetric -----------------------------------------------------------

||| Perm is symmetric
permSymm: Perm as bs -> Perm bs as
permSymm {as = []} {bs = []} PermNil = PermNil
permSymm {as = x :: r1} {bs = l2 ++ x :: r2} (PermInsert permNoX) =
 let recur: Perm (l2 ++ r2) r1 = permSymm permNoX
 in permInsertAnywhere {l2 = []} recur 

||| You can drop an element x from permuted lists and get permuted lists
permDropAnywhere:
  Perm (l1 ++ x :: r1) (l2 ++ x :: r2) -> Perm (l1 ++ r1) (l2 ++ r2)
permDropAnywhere permX =
  permDropAnywhere' permX Refl Refl
  where
  permDropAnywhere':
    Perm vl vr -> vl = (l1 ++ x :: r1) -> vr = (l2 ++ x :: r2) ->
      Perm (l1 ++ r1) (l2 ++ r2)
  permDropAnywhere' {l1 = []} PermNil eqL _ = void (consIsntNil (sym eqL))
  permDropAnywhere' {l1 = _ :: _} PermNil eqL _ = void (consIsntNil (sym eqL))
  permDropAnywhere' {l1 = []} perm Refl Refl = permDrop perm
  permDropAnywhere' {x} {l1 = y :: ys} {r1} {l2} {r2}
       (PermInsert {x = x'} {r1 = r1'} {l2 = l2'} {r2 = r2'} permNoX) eqL eqR =
    case eqL of
      Refl =>
        case equalConcats3 eqR of
          Left (Refl,Refl) =>
            let permRev: Perm (l2 ++ r2) (ys ++ y :: r1) = permSymm permNoX
                swap: Perm (l2 ++ r2) (y :: r1 ++ ys) = permSwap permRev
                swap1: Perm (l2 ++ r2) (y :: ys ++ r1) =
                  permSwapAfter {as = [y]} swap
            in  permSymm swap1
          Right (Left (m ** ms ** (Refl,Refl))) =>
            let reassoc1: (l2' ++ ms ++ x :: r2 = (l2' ++ ms) ++ x :: r2) =
                  appendAssociative l2' ms (x :: r2)
                perm1: Perm (ys ++ x :: r1) ((l2' ++ ms) ++ x :: r2) =
                  rewrite sym reassoc1 in permNoX
                recur: Perm (ys ++ r1) ((l2' ++ ms) ++ r2) =
                  permDropAnywhere' perm1 Refl Refl
                reassoc2: (l2' ++ ms ++ r2 = (l2' ++ ms) ++ r2) =
                  appendAssociative l2' ms r2
                recur1: Perm (ys ++ r1) (l2' ++ ms ++ r2) =
                  rewrite reassoc2 in recur
                insert: Perm (m :: ys ++ r1) (l2' ++ m :: ms ++ r2) =
                  PermInsert recur1
                reassoc3: (l2' ++ m :: ms ++ r2 = (l2' ++ m :: ms) ++ r2) =
                  appendAssociative l2' (m :: ms) r2
            in  rewrite sym reassoc3 in insert
          Right (Right (m ** ms ** (Refl,Refl))) =>
            let reassoc1: (l2 ++ m :: ms ++ r2'= (l2 ++ m :: ms) ++ r2') =
                  appendAssociative l2 (m :: ms) r2'
                perm1: Perm (ys ++ m :: r1) (l2 ++ m :: ms ++ r2') =
                  rewrite reassoc1 in permNoX
                recur: Perm (ys ++ r1) (l2 ++ ms ++ r2') =
                  permDropAnywhere' perm1 Refl Refl
                reassoc2: (l2 ++ ms ++ r2' = (l2 ++ ms) ++ r2') =
                  appendAssociative l2 ms r2'
                recur1: Perm (ys ++ r1) ((l2 ++ ms) ++ r2') =
                  rewrite sym reassoc2 in recur
                insert: Perm (y :: ys ++ r1) ((l2 ++ ms) ++ y :: r2') =
                  PermInsert recur1
                reassoc3: (l2 ++ ms ++ y :: r2' = (l2 ++ ms) ++ y :: r2') =
                  appendAssociative l2 ms (y :: r2')
            in  rewrite reassoc3 in insert

-- Perm is transitive, and therefore an equivalence relation -------------------
-- (permRefl and permSymm are defined above) -----------------------------------

||| Perm is transitive
permTrans: Perm as bs -> Perm bs cs -> Perm as cs
permTrans {as = []} {bs = []} {cs} PermNil bsCs =
  case bsCs of
    PermNil => bsCs
permTrans {as = x :: r1} {bs = l2 ++ x :: r2} {cs} (PermInsert permNoX) bsCs =
  let xInBs: Elem x (l2 ++ x :: r2) = elemBetween
      xInCs: Elem x cs = elemInAllPerms xInBs bsCs
      (l3 ** r3 ** Refl) = elemBetweenWhat xInCs
      perm23: Perm (l2 ++ r2) (l3 ++ r3) = permDropAnywhere bsCs
      recur: Perm r1 (l3 ++ r3) = permTrans permNoX perm23
  in  PermInsert recur
