||| General definitions and theorems about relations
module Control.Relations.TransitiveClosure
import Control.Relations.Basics
import Control.Relations.ClosureOperators

%default total
%access public

||| Proof that a relation is the transitive closure of another
IsTransitiveClosureOf : (tcrel, rel : Rel a) -> Type
IsTransitiveClosureOf = IsClosureUnderPredOf Transitive

trns : {tcrel, rel : Rel a} -> IsTransitiveClosureOf tcrel rel -> Transitive tcrel
trns itc = satisfiesP itc

||| `IsTransitiveClosureOf` respects `Equivalent`
isTransitiveClosureOfRespEq : (r1,r2 : Rel a) ->
                              IsTransitiveClosureOf r1 rel ->
                              r1 `Equivalent` r2 ->
                              IsTransitiveClosureOf r2 rel
isTransitiveClosureOfRespEq {a} {rel} r1 r2 r1tcrel r1r2 =
    equivToClosureClosure {a} Transitive transitiveRespectsEquiv r1 r2 rel r1tcrel r1r2

||| Proof that a function on relations is the transitive closure
IsTransitiveClosure : (tc : Rel a -> Rel a) -> Type
IsTransitiveClosure = IsClosureUnderPred Transitive

transitiveClosureIsClosureOperator : (tc : Rel a -> Rel a) ->
                                     IsTransitiveClosure tc ->
                                     ClosureOperator tc
transitiveClosureIsClosureOperator tc isAlwaysTC = closureUnderPredIsClosureOperator Transitive tc isAlwaysTC

||| One common construction of the transitive closure
data TC : Rel a -> Rel a where
  TCIncl : rel x y -> TC rel x y
  TCTrans : {y : a} -> TC rel x y -> TC rel y z -> TC rel x z

tcTransitive : {rel : Rel a} -> Transitive (TC rel)
tcTransitive = (\_, _, _, xRy, yRz => TCTrans xRy yRz)

tcCoarsest : {rel, rel' : Rel a} -> rel `Coarser` rel' -> Transitive rel' ->
             TC rel `Coarser` rel'
tcCoarsest rsubr' tr' x y (TCIncl xy) = rsubr' _ _ xy
tcCoarsest rsubr' tr' x z (TCTrans {y} xy yz) =
  let foo = tcCoarsest rsubr' tr' x y xy
      bar = tcCoarsest rsubr' tr' y z yz
  in tr' _ _ _ foo bar

||| `TC` is in fact the transitive closure
tcIsTransitiveClosure : IsTransitiveClosure TC
tcIsTransitiveClosure rel = MkIsClosureUnderPredOf (\x,y=>TCIncl) tcTransitive
                              (\r, relr, trnsr, x, y, tcrelxy => tcCoarsest relr trnsr x y tcrelxy)

||| `TC` is a closure operator
tcIsClosureOperator : ClosureOperator TC
tcIsClosureOperator = closureUnderPredIsClosureOperator Transitive TC tcIsTransitiveClosure

||| The transitive closure of a reflexive relation is reflexive.
tcReflRefl : {rel : Rel a} -> Reflexive eq rel -> tc `IsTransitiveClosureOf` rel -> Reflexive eq tc
tcReflRefl rfler (MkIsClosureUnderPredOf tcfiner tctrns tccoarsest) x y eqxy =
  tcfiner x y (rfler x y eqxy)

||| Alternative construction of transitive closure
data TC' : Rel a -> Rel a where
  TCIncl' : rel x y -> TC' rel x y
  TCTrans' : rel x y -> TC' rel y z -> TC' rel x z

tcTransitive' : {rel : Rel a} -> Transitive (TC' rel)
tcTransitive' x y z (TCIncl' xy) yz = TCTrans' xy yz
tcTransitive' x y z (TCTrans' {y=y'} xy' y'y) yz = 
    TCTrans' xy' (tcTransitive' y' y z y'y yz)

tcThenTC' : {rel : Rel a} -> TC rel `Coarser` TC' rel
tcThenTC' {a} {rel} = tcCoarsest {rel} {rel'=TC' rel} (\x,y,xy=>TCIncl' xy) (tcTransitive' {rel})

tc'ThenTC : {rel : Rel a} -> TC' rel `Coarser` TC rel
tc'ThenTC x z (TCIncl' xz) = TCIncl xz
tc'ThenTC x z (TCTrans' {y} xy yz) = TCTrans (TCIncl xy) (tc'ThenTC y z yz)

tcEquivTC' : {rel : Rel a} -> Equivalent (TC rel) (TC' rel)
tcEquivTC' = MkEquivalent tcThenTC' tc'ThenTC

||| Transitive closure by the second definition is a closure operator
tc'IsClosureOperator : ClosureOperator TC'
tc'IsClosureOperator = equivClosureClosure TC TC' (\rel => tcEquivTC' {rel}) tcIsClosureOperator

||| The alternative construction of the transitive closure is in fact
||| the transitive closure.
tc'IsTransitiveClosure : IsTransitiveClosure {a} TC'
tc'IsTransitiveClosure {a} rel =
     equivToClosureClosure {a} Transitive transitiveRespectsEquiv
            (TC rel) (TC' rel) rel (tcIsTransitiveClosure rel) tcEquivTC'

||| The transitive closure of the dual of a relation is the
||| dual of its transitive closure.
dualOfTransitiveClosureIsTransitiveClosureOfDual : {rel : Rel a} ->
         IsTransitiveClosure tc ->
         flip (tc rel) `Equivalent` tc (flip rel)
dualOfTransitiveClosureIsTransitiveClosureOfDual {a} {rel} {tc} tctc =
  let foo = closuresUnderSamePredEquiv Transitive (tc rel) (flip (tc (flip rel))) rel (tctc rel) fliptcflipistc
      bar = flipPreservesEquivalence foo
      baz = flipFlip {rel=tc (flip rel)}
  in trns equivalentIsEquivalence _ _ _ bar baz
  where
    fliptcflipistc : IsClosureUnderPredOf Transitive (flip (tc (flip rel))) rel
    fliptcflipistc with (tctc (flip rel))
      fliptcflipistc | (MkIsClosureUnderPredOf ftcfiner ftctrans ftccoarsest) =
        MkIsClosureUnderPredOf
         (\x,y,relxy => ftcfiner y x relxy)
         transFliptcflip
         coars
        where
          transFliptcflip : Transitive (flip (tc (flip rel)))
          transFliptcflip x y z xy yz = ftctrans z y x yz xy

          coars : (r : Rel a) -> rel `Coarser` r -> Transitive r ->
           (x, y : a) -> tc (flip rel) y x -> r x y
          coars r relr rtrns x y tcfrelyx = ftccoarsest (flip r) (\q,s,sq=>relr s q sq) trnsflipr y x tcfrelyx
            where
              trnsflipr : Transitive (flip r)
              trnsflipr x y z yx zy = rtrns z y x zy yx
