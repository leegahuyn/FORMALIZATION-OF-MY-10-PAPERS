import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleConstantRootHOne
import PrimalitySheafVerification.ManuscriptAudit.EtaleKummerCyclotomicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.EtaleKummerCyclicCoordinates

/-! The actual untwisted cyclic coefficient pullback and actual unit
pullback differ under the Kummer label by the cyclotomic scalar. -/

namespace ManuscriptAudit.FullEtaleCyclicFrobeniusLabel

open AlgebraicGeometry CategoryTheory Opposite
open KummerUnitsSheaf FullEtaleConstantRootLabel FullEtaleConstantRootHOne
open OpenEtaleUnitHOneComposition EtaleKummerCyclicCoordinates
open EtaleKummerCyclotomicFrobenius CoherentPrimitiveRoots

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev C (X : Scheme.{0}) := constantSheaf X.smallEtaleTopology A

private theorem constant_map_nsmul (X : Scheme.{0}) (M : A) (a : ℕ) :
    (C X).map (a • 𝟙 M) = a • 𝟙 ((C X).obj M) := by
  let P := Functor.const X.Etaleᵒᵖ
  let L := presheafToSheaf X.smallEtaleTopology A
  letI : L.Additive := Functor.additive_of_preserves_binary_products L
  have h : P.map (a • 𝟙 M) = a • 𝟙 (P.obj M) := by
    apply NatTrans.ext
    funext T
    rfl
  change L.map (P.map (a • 𝟙 M)) = a • 𝟙 (L.obj (P.obj M))
  rw [h, Functor.map_nsmul, L.map_id]

private theorem constantHOne_nsmul (X : Scheme.{0}) (M : A) (a : ℕ)
    (x : Sheaf.H ((C X).obj M) 1) :
    Sheaf.H.map ((C X).map (a • 𝟙 M)) 1 x = a • x := by
  let H := Sheaf.functorH X.smallEtaleTopology 1
  change (H.map ((C X).map (a • 𝟙 M))).hom x = _
  rw [constant_map_nsmul, Functor.map_nsmul, H.map_id] <;> rfl

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev σ (m : ℕ) := ((FiniteField.frobeniusAlgHom k K) ^ m).toRingHom

private theorem cyclicCoefficient_scalar (n m : ℕ) :
    (cyclicIso K l n).hom ≫ fieldRootMap (σ k K m) (l ^ n) =
      ((Fintype.card k) ^ m • 𝟙 (cyclicGroup l n)) ≫ (cyclicIso K l n).hom := by
  apply AddCommGrpCat.ext
  intro a
  apply Additive.ext
  exact coherent_frobenius_scalar k K l n m a

variable {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (b : X ⟶ Spec (CommRingCat.of K)) (b' : U ⟶ Spec (CommRingCat.of K))

/-- The actual cyclic Kummer label into the full unit sheaf. -/
def cyclicUnitLabel (n : ℕ) :
    (C X).obj (cyclicGroup l n) ⟶ fullCoordinateUnitSheaf X :=
  (C X).map (cyclicIso K l n).hom ≫ unitLabel b (l ^ n)

/-- At every level, actual pullback on unit cohomology is cyclotomic
times actual untwisted cyclic pullback under the literal Kummer label. -/
theorem cyclicUnitLabel_pullback (n m : ℕ)
    (h : j ≫ b = b' ≫ Spec.map (CommRingCat.ofHom (σ k K m)))
    (x : Sheaf.H ((C X).obj (cyclicGroup l n)) 1) :
    unitPullback j (Sheaf.H.map (cyclicUnitLabel K l b n) 1 x) =
      (Fintype.card k) ^ m •
        Sheaf.H.map (cyclicUnitLabel K l b' n) 1 (constantPullback j (cyclicGroup l n) x) := by
  let f := (cyclicIso K l n).hom
  let g := fieldRootMap (σ k K m) (l ^ n)
  let r := (Fintype.card k) ^ m
  let y := constantPullback j (cyclicGroup l n) x
  let u := unitLabel b' (l ^ n)
  have hfg : f ≫ g = (r • 𝟙 (cyclicGroup l n)) ≫ f :=
    cyclicCoefficient_scalar k K l n m
  calc
    _ = Sheaf.H.map u 1 (Sheaf.H.map ((C U).map (f ≫ g)) 1 y) := by
      rw [cyclicUnitLabel, Sheaf.H.map_comp_apply, unitLabel_pullback j b b' (σ k K m) h,
        constantPullback_coeff j f, Functor.map_comp, Sheaf.H.map_comp_apply]
    _ = Sheaf.H.map u 1 (Sheaf.H.map ((C U).map f) 1 (r • y)) := by
      rw [hfg, Functor.map_comp, Sheaf.H.map_comp_apply,
        constantHOne_nsmul]
    _ = _ := by
      rw [← Sheaf.H.map_comp_apply]
      exact (Sheaf.H.map (cyclicUnitLabel K l b' n) 1).map_nsmul y r

end

end ManuscriptAudit.FullEtaleCyclicFrobeniusLabel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleCyclicFrobeniusLabel.cyclicUnitLabel_pullback
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
