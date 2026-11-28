import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHigher
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoPositiveCharacteristic
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicMilnorPositive

/-! In positive characteristic, the actual proper cusp has no native
cohomology in degrees at least three, at finite residue levels and
with its original continuous adic coefficients. -/

namespace ManuscriptAudit.CuspNativeProperHigher

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspChartIntersection (overlapIsoLaurent)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep nativeCompatible reductionMap)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteConstant (nativeResidueIso)
open OpenProetaleExtension (restriction)
open ProetaleMayerVietorisConnecting (connecting_surjective)
open CuspNativeAdicHTwoLower (adicInclusion)
open CuspNativeAdicHTwoReduction (residueInclusion reduction_adicInclusion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (p l : ℕ) [hp : Fact p.Prime] [hK : CharP K p] [Fact l.Prime] [NeZero (l : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev Y := affineCusp K
private abbrev Z := Spec (CommRingCat.of (Polynomial K))
private abbrev W := pullback (affineOpen K) (lineOpen K)

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩
local instance castResidue (r : ℕ) : NeZero ((l ^ r : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero r (NeZero.ne (l : K))⟩

include p hp hK in
private theorem cusp_succ (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (Y K) l r) (n + 1)) := by
  let e := (cohomologyIso (nativeResidueIso (Y K) l r).symm (n + 1)).trans
    ((CuspProetaleCohomologyEquivalence.cyclicEquiv K p (l ^ r) (n + 1)).trans
      (cohomologyIso (nativeResidueIso (Z K) l r) (n + 1)))
  have h := AffineNativeResidueHigher.affineLine_succ_subsingleton K l r n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

private theorem overlap_add_two (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (W K) l r) (n + 2)) := by
  let e := IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : Polynomial K))
    (LaurentPolynomial K) (Localization.Away (Polynomial.X : Polynomial K))
  let iso := overlapIsoLaurent K ≪≫ (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).symm
  let k := SchemeIsoProetaleCohomology.continuousCohomologyEquiv iso (ZMod (l ^ r)) (n + 2)
  have h := AffineNativeResidueHigher.principalOpen_add_two_subsingleton K l r
    Polynomial.X Polynomial.X_ne_zero n
  exact ⟨fun x y ↦ k.injective (h.elim (k x) (k y))⟩

private def restrictionEquiv {U : Scheme.{0}} (j : U ⟶ X K) [IsOpenImmersion j]
    (r n : ℕ) :
    Sheaf.H ((restriction j A).obj (finiteCoefficient (X K) l r)) n ≃+
      Sheaf.H (finiteCoefficient U l r) n :=
  cohomologyIso (restrictionFunctionsIso j (ZMod (l ^ r))) n

include p hp hK in
set_option maxHeartbeats 6100000 in
/-- The actual finite proper cusp cohomology vanishes in degree n + 3. -/
theorem residue_add_three_subsingleton (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X K) l r) (n + 3)) := by
  let j := affineOpen K
  let k := lineOpen K
  let w := overlapOpen K
  letI := cusp_succ K p l r (n + 2)
  letI := AffineNativeResidueHigher.affineLine_succ_subsingleton K l r (n + 2)
  let hY : Subsingleton (Sheaf.H ((restriction j A).obj (finiteCoefficient (X K) l r)) (n + 3)) :=
    (restrictionEquiv K l j r (n + 3)).injective.subsingleton
  let hZ : Subsingleton (Sheaf.H ((restriction k A).obj (finiteCoefficient (X K) l r)) (n + 3)) :=
    (restrictionEquiv K l k r (n + 3)).injective.subsingleton
  letI := overlap_add_two K l r n
  letI : Subsingleton (Sheaf.H ((restriction w A).obj (finiteCoefficient (X K) l r)) (n + 2)) :=
    (restrictionEquiv K l w r (n + 2)).injective.subsingleton
  exact (connecting_surjective j k w (fstLeg K) (sndLeg K) (overlap K)
    (cover K) (finiteCoefficient (X K) l r) (n + 2) hY hZ).subsingleton

include p hp hK in
private theorem step_add_two_surjective (n r : ℕ) :
    Function.Surjective (nativeStep (X K) l (n + 2) r) := by
  cases n with
  | zero =>
      intro x
      obtain ⟨a, ha⟩ := CuspNativeAdicHTwoPositiveCharacteristic.residueInclusion_surjective K p l r x
      let z : ℤ_[l] := a.val
      let T := reductionMap (X K) l 2 (adicInclusion K l z)
      refine ⟨T.val (r + 1), (T.property r).trans ?_⟩
      change (reductionMap (X K) l 2 (adicInclusion K l z)).val r = x
      rw [reduction_adicInclusion, show z = (a.val : ℤ_[l]) from rfl, map_natCast,
        ZMod.natCast_zmod_val, ha]
  | succ m =>
      intro x
      exact ⟨0, (residue_add_three_subsingleton K p l r m).elim _ _⟩

include p hp hK in
/-- The genuine continuous adic groups in degrees at least three also vanish. -/
theorem adic_add_three_subsingleton (n : ℕ) :
    Subsingleton ((X K).EllAdicCohomology l (n + 3)) := by
  let e := ProetaleAdicMilnorPositive.reductionEquiv (X K) l (n + 1)
    (step_add_two_surjective K p l n)
  have h : Subsingleton (nativeCompatible (X K) l (n + 3)) :=
    ⟨fun x y ↦ Subtype.ext (funext fun r ↦
      (residue_add_three_subsingleton K p l r n).elim _ _)⟩
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

end
end ManuscriptAudit.CuspNativeProperHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeProperHigher.residue_add_three_subsingleton,
      ``ManuscriptAudit.CuspNativeProperHigher.adic_add_three_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
