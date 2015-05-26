||| Well-founded recursion.
|||
||| This is to let us implement some functions that don't have trivial
||| recursion patterns over datatypes, but instead are using some
||| other metric of size.
module WellFounded
import Control.Relations.Basics
import Control.Relations.ClosureOperators
import Control.Relations.TransitiveClosure

%default total
%access public

||| A predicate on a type
|||
||| @ a an arbitrary type
Pred : (a : Type) -> Type
Pred a = a -> Type

||| Express that a predicate is a subset of another
|||
||| @ a an arbitrary type
||| @ P1 a predicate on a
||| @ P2 a predicate on a proven to be less restrictive
Subset : {a : Type} -> (P1, P2 : Pred a) -> Type
Subset {a} P1 P2 = {x : a} -> P1 x -> P2 x

||| Accessibility: some element `x` is accessible if all `y` such that
||| `rel y x` are themselves accessible.
|||
||| @ a the type of elements
||| @ rel a relation on a
||| @ x the acessible element
data Accessible : (rel : a -> a -> Type) -> (x : a) -> Type where
  ||| Accessibility
  |||
  ||| @ x the accessible element
  ||| @ acc' a demonstration that all smaller elements are also accessible
  Access : (acc' : (y : a) -> rel y x -> Accessible rel y) ->
           Accessible rel x

||| A relation `rel` on `a` is well-founded if all elements of `a` are
||| acessible.
|||
||| @ rel the well-founded relation
WellFounded : (rel : a -> a -> Type) -> Type
WellFounded rel = (x : _) -> Accessible rel x

||| An induction principle for accessibility.
|||
||| This allows us to recurse over the subset of some type that is
||| accessible according to some relation, producing a dependent type
||| as a result.
|||
||| @ rel the well-founded relation
||| @ step how to take steps on reducing arguments
||| @ z the starting point
accInd : {rel : a -> a -> Type} -> {P : a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
         (z : a) -> Accessible rel z -> P z
accInd step z (Access f) =
  step z $ \y, lt => accInd step y (f y lt)

||| A recursor over accessibility.
|||
||| This allows us to recurse over the subset of some type that is
||| accessible according to some relation.
|||
||| @ rel the well-founded relation
||| @ step how to take steps on reducing arguments
||| @ z the starting point
accRec : {rel : a -> a -> Type} ->
         (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
         (z : a) -> Accessible rel z -> b
accRec {b} = accInd {P = const b}

wfInd : {rel : Rel a} -> {P : a -> Type} -> WellFounded rel ->
        (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
        (x : a) -> P x
wfInd wfR step x = accInd step x (wfR x)

||| Use well-foundedness of a relation to write terminating operations.
|||
||| @ rel a well-founded relation
wfRec : WellFounded rel ->
        (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
        a -> b
wfRec {b} = wfInd {P = const b}

parameters (r1 : Rel a, r2 : Rel a, f : r1 `Coarser` r2)
  ||| An element accessible relative to a relation is accessible relative
  ||| to any coarser relation.
  |||
  ||| @ r2 A relation
  ||| @ r1 A relation
  ||| @ f Proof that `r1` is coarser than `r2`
  ||| @ p An element
  ||| @ accr2p Proof that `p` is accessible relative to `r2`
  coarserAcc : (p : a) -> (accr2p : Accessible r2 p) -> Accessible r1 p
  coarserAcc p (Access g) = Access (\z, r1zp =>
                                coarserAcc z (g z (f z p r1zp)))

  ||| A relation that is coarser than a well-founded relation is
  ||| well-founded.
  |||
  ||| @ r2 A relation
  ||| @ r1 A relation
  ||| @ f Proof that `r1` is coarser than `r2`
  ||| @ wf Proof that `r2` is well-founded
  coarserWF : (wf : WellFounded r2) -> WellFounded r1
  coarserWF wfr2 x = coarserAcc x (wfr2 x)

parameters (r : Rel b, f : a -> b)
  ||| If the image of an element under a function is accessible relative
  ||| to a relation, then the element is accessible under the inverse
  ||| image of the relation.
  inverseImageAcc : (x : a) -> Accessible rb (f x) -> Accessible (rb `On` f) x
  inverseImageAcc x (Access g) = Access (\z, ryx =>
                                 inverseImageAcc z (g (f z) ryx))

  ||| The inverse image of a well-founded relation under a function is
  ||| well-founded.
  inverseImageWF : WellFounded rel -> WellFounded (rel `On` f)
  inverseImageWF wfr x = inverseImageAcc x (wfr (f x))

transDownwardsClosed : {rel : Rel a} -> (tr : Transitive rel) -> Accessible rel y ->
                       x `rel` y -> Accessible rel x
transDownwardsClosed tr (Access acc) xRy = Access (\z, zRx => acc z (tr _ _ _ zRx xRy))

transitiveClosureDownwardsClosed : {rel : Rel a} -> tc `IsTransitiveClosureOf` rel ->
                                   Accessible tc y ->
                                   tc x y ->
                                   Accessible tc x
transitiveClosureDownwardsClosed {tc} tctc = transDownwardsClosed {rel=tc} (trns tctc)

tcDownwardsClosed : {rel : Rel a} -> Accessible (TC rel) y ->
                     TC rel x y -> Accessible (TC rel) x
tcDownwardsClosed {a} {rel} acctcy tcrelxy = transitiveClosureDownwardsClosed (tcIsTransitiveClosure rel) acctcy tcrelxy

tcAcc' : {rel : Rel a} -> Accessible rel x -> (y : a) -> TC rel y x -> Accessible (TC rel) y
tcAcc' {rel} (Access acc') y (TCIncl yRx) = Access (tcAcc' {rel} (acc' y yRx))
tcAcc' {rel = rel} {x = x} accx y (TCTrans {y=yk} {z=x} yRz zRx) =
  let hmm = tcAcc' accx yk zRx
  in tcDownwardsClosed hmm yRz

tcAcc : Accessible rel x -> Accessible (TC rel) x
tcAcc accx = Access (tcAcc' accx)

transitiveClosureAcc : {rel : Rel a} -> tc `IsTransitiveClosureOf` rel ->
                       Accessible rel x -> Accessible tc x
transitiveClosureAcc {a} {rel} {tc} {x} tctc accrelx =
  coarserAcc tc (TC rel)
             (to $ closuresUnderSamePredEquiv Transitive tc (TC rel) rel tctc (tcIsTransitiveClosure rel))
              x (tcAcc accrelx)

tcWellFounded : {rel : Rel a} -> WellFounded rel -> WellFounded (TC rel)
tcWellFounded {rel} wfr x = tcAcc {rel} (wfr x)

transitiveClosureWellFounded : {rel : Rel a} -> tc `IsTransitiveClosureOf` rel ->
                               WellFounded rel -> WellFounded tc
transitiveClosureWellFounded {rel} tctc wfr x = transitiveClosureAcc {rel} tctc (wfr x)

parameters (A : Type, B : A -> Type, RelA : Rel A, RelB : (x : A) -> Rel (B x))
  data Lexic : Rel (Sigma A B) where
    Lefty : RelA x1 x2 -> Lexic (MkSigma x1 y1) (MkSigma x2 y2)
    Righty : RelB x y1 y2 -> Lexic (MkSigma x y1) (MkSigma x y2)


  lexicAcc' : Accessible RelA x -> Accessible (RelB x) y ->
              ({x : A} -> ((y : B x) -> Accessible (RelB x) y)) ->
              (z : Sigma A B) -> z `Lexic` MkSigma x y -> Accessible Lexic z
  lexicAcc' (Access accA') accrbxy wfB _ (Lefty xpRx) = Access (lexicAcc' (accA' _ xpRx) (wfB _) wfB)
  lexicAcc' accA (Access accB') wfB _ (Righty ypRy) = Access (lexicAcc' accA (accB' _ ypRy) wfB)

-- It would be nice to use WellFounded (RelB x) as an argument, but that
-- crashes the compiler with a scope error.
  lexicAcc : Accessible RelA x -> ({x : A} -> ((y : B x) -> Accessible (RelB x) y)) ->
                                  Accessible Lexic (MkSigma x y)
  lexicAcc {x} accA wfB = Access (lexicAcc' accA (wfB _) wfB)

  lexicWellFounded : WellFounded RelA -> ({x : A} -> WellFounded (RelB x)) ->
                                           WellFounded Lexic
  lexicWellFounded wfA wfB (MkSigma p q) = lexicAcc (wfA p) wfB

||| Convert a pair to a dependent pair.
pairToSigma : (a, b) -> Sigma a (\_ => b)
pairToSigma (a, b) = MkSigma a b

||| A specialization of lexicographic ordering to simple pairs. This "open" form
||| makes its properties easy to prove, but also seems to make it hard to use.
||| The `LexicPair` version hides this in a datatype, which seems to make it easier
||| to handle.
LexicPair' : Rel a -> Rel b -> Rel (a, b)
LexicPair' {a} {b} ra rb = Lexic a (\_ => b) ra (\_ => rb) `On` pairToSigma

lexicPairAcc' : {x : a} -> {y : b} -> Accessible relA x -> WellFounded relB -> Accessible (LexicPair' relA relB) (x,y)
lexicPairAcc' {a} {b} {x} {y} {relA} {relB} accA wfB =
  inverseImageAcc (Lexic a (\_ => b) relA (\_ => relB)) pairToSigma (x,y)
          (lexicAcc a (\_ => b) relA (\_ => relB) accA wfB)

lexicPairWF' : WellFounded relA -> WellFounded relB -> WellFounded (LexicPair' relA relB)
lexicPairWF' wfA wfB (x,y) = lexicPairAcc' (wfA x) wfB

||| A specialization of lexicographic ordering to pairs. Where it applies, this
||| should be substantially easier to use. A more elementary implementation of this idea
||| is given by `LexicPairSimple`, which is proven equivalent by `mkLexicPair` and
||| `getLexicPair`.
data LexicPair : Rel a -> Rel b -> Rel (a, b) where
  MkLexicPair : {p,q : (a,b)} -> LexicPair' ra rb p q ->
                LexicPair ra rb p q

||| A simple expression of the lexicographic ordering of pairs.
data LexicPairSimple : Rel a -> Rel b -> Rel (a, b) where
  LeftySimple : relA x1 x2 -> LexicPairSimple relA relB (x1, y1) (x2, y2)
  RightySimple : relB y1 y2 -> LexicPairSimple relA relB (x, y1) (x, y2)

||| Convert a `LexicPairSimple` to a `LexicPair`
mkLexicPair : {relA : Rel a} -> {relB : Rel b} ->
          {x1, x2 : a} -> {y1, y2 : b} ->
          LexicPairSimple relA relB (x1, y1) (x2, y2) ->
          LexicPair relA relB (x1, y1) (x2, y2)
mkLexicPair (LeftySimple x1x2) = MkLexicPair (Lefty _ _ _ _ x1x2)
mkLexicPair (RightySimple y1y2) = MkLexicPair (Righty _ _ _ _ y1y2)

||| Convert a `LexicPair` to a `LexicPairSimple`
getLexicPair : {relA : Rel a} -> {relB : Rel b} ->
               {x1, x2 : a} -> {y1, y2 : b} ->
               (pairpair : LexicPair relA relB (x1, y1) (x2, y2)) ->
               LexicPairSimple relA relB (x1, y1) (x2, y2)
getLexicPair (MkLexicPair (Lefty _ _ _ _ x1x2)) = LeftySimple x1x2
getLexicPair (MkLexicPair (Righty _ _ _ _ y1y2)) = RightySimple y1y2



lexicCoarserLexic' : {a,b:Type} -> (relA : Rel a) -> (relB : Rel b) ->
                      LexicPair relA relB `Coarser` LexicPair' relA relB
lexicCoarserLexic' relA relB (x1,y1) (x2,y2) (MkLexicPair lp) = lp

lexicpCoarserLexic : {a,b:Type} -> (relA : Rel a) -> (relB : Rel b) ->
                      LexicPair' relA relB `Coarser` LexicPair relA relB
lexicpCoarserLexic relA relB (x1,y1) (x2,y2) lp = MkLexicPair lp

lexicPairAcc : {x : a} -> {y : b} -> Accessible relA x -> WellFounded relB -> Accessible (LexicPair relA relB) (x,y)
lexicPairAcc {relA = relA} {relB = relB} {x} {y} accA wfB =
  coarserAcc (LexicPair relA relB) (LexicPair' relA relB) (lexicCoarserLexic' relA relB) (x,y) (lexicPairAcc' accA wfB)

lexicPairWF : WellFounded relA -> WellFounded relB -> WellFounded (LexicPair relA relB)
lexicPairWF wfA wfB (x,y) = lexicPairAcc (wfA x) wfB

lexicPairSimpleAcc : {x : a} -> {y : b} -> Accessible relA x -> WellFounded relB ->
                     Accessible (LexicPairSimple relA relB) (x,y)
lexicPairSimpleAcc {relA = relA} {relB = relB} {x} {y} accA wfB =
  coarserAcc (LexicPairSimple relA relB) (LexicPair relA relB) (\(x1,y1), (x2,y2) => mkLexicPair {relA} {relB}) (x,y) (lexicPairAcc accA wfB)

lexicPairSimpleWF : WellFounded relA -> WellFounded relB -> WellFounded (LexicPairSimple relA relB)
lexicPairSimpleWF wfA wfB (x,y) = lexicPairSimpleAcc (wfA x) wfB

||| Given a relation `relA` on `a` and a relation `relB` on `b`, we can form a relation
||| on `(a,b)` by letting `WkProd relA relB (a1, b1) (a2, b2)` if either:
|||
||| * `relA a1 a2` and `b1 = b2`
||| * `relA a1 a2` and `relB b1 b2`
||| * `relB b1 b2` and `a1 = a2`
data WkProd : Rel a -> Rel b -> Rel (a, b) where
  FirstR : a1 `relA` a2 -> WkProd relA relB (a1, b) (a2, b)
  SecondR : b1 `relB` b2 -> WkProd relA relB (a, b1) (a, b2)
  BothR : a1 `relA` a2 -> b1 `relB` b2 -> WkProd relA relB (a1, b1) (a2, b2)

wkProdCoarserLex : {relA : Rel a} -> {relB : Rel b} ->
                   WkProd relA relB `Coarser` (LexicPair relA relB)
wkProdCoarserLex (a1, b) (a2, b) (FirstR a1a2) = MkLexicPair $ Lefty _ _ _ _ a1a2
wkProdCoarserLex (a, b1) (a, b2) (SecondR b1b2) = MkLexicPair $ Righty _ _ _ _ b1b2
wkProdCoarserLex (a1, b1) (a2, b2) (BothR a1a2 b1b2) = MkLexicPair $ Lefty _ _ _ _ a1a2

||| The `WkProd` of two relations is coarser than their lexicographic product
wkProdWellFounded : {r1 : Rel a} -> {r2 : Rel b} -> WellFounded r1 -> WellFounded r2 ->
                    WellFounded {a = (a,b)} (WkProd r1 r2)
wkProdWellFounded {r1} {r2} wfr1 wfr2 = coarserWF (WkProd r1 r2) (LexicPair r1 r2) wkProdCoarserLex
                                        (lexicPairWF wfr1 wfr2)

private
data Irref1 : Rel a -> a -> Type where
  MkIrref1 : (x `rel` x -> Void) -> Irref1 rel x

||| A well-founded relation is irreflexive.
abstract
wellFoundedIrreflexive : {rel : Rel a} -> WellFounded rel -> (x : a) -> x `rel` x -> Void
wellFoundedIrreflexive {rel} wfRel x xRx
  with (wfInd {rel} wfRel {P = Irref1 rel} (\z, f => MkIrref1 (\zRz =>
             case f z zRz of
                  MkIrref1 g => g zRz)) x)
  wellFoundedIrreflexive {rel = rel} wfRel x xRx | (MkIrref1 f) = f xRx
