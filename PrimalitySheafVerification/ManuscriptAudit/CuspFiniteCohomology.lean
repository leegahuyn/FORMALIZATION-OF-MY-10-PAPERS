import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Finiteness.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportEuler
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAllHigher
import PrimalitySheafVerification.ManuscriptAudit.CuspHTwoCyclic

/-! Exact compact-support dimensions for the actual cusp and its puncture. -/

namespace ManuscriptAudit.CuspFiniteCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProperCompactification CuspCompactSupportSequence
open OpenEtaleExtension SmallEtaleGeometricBaseChange
open scoped BigOperators

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] CuspCompactSupportEuler.cuspModule CuspCompactSupportEuler.punctureModule

variable (K : Type) [Field K] [kClosed : IsAlgClosed K]
variable (p : ℕ) [pPrime : Fact p.Prime] [pChar : CharP K p]
variable (ℓ : ℕ) [Fact ℓ.Prime] [coeffNZ : NeZero (ℓ : K)]

private abbrev G := AddCommGrpCat.{0}
private abbrev M : G := AddCommGrpCat.of (ULift.{0} (ZMod ℓ))
private abbrev m : G := AddCommGrpCat.of (ZMod ℓ)

private def coefficientIso : M ℓ ≅ m ℓ :=
  (show ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ from
    { toFun := ULift.down, invFun := ULift.up, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }).toAddCommGrpIso

private def extensionCohomologyEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) :
    Sheaf.H ((extensionByZero j G).obj ((constantSheaf U.smallEtaleTopology G).obj (M ℓ))) n ≃+
      Sheaf.H ((extensionByZero j G).obj ((constantSheaf U.smallEtaleTopology G).obj (m ℓ))) n :=
  ((Sheaf.functorH X.smallEtaleTopology n).mapIso
    ((extensionByZero j G).mapIso
      ((constantSheaf U.smallEtaleTopology G).mapIso (coefficientIso ℓ)))).addCommGroupIsoToAddEquiv

private def cuspCoefficients (n : ℕ) : cuspHc K (M ℓ) n ≃+ cuspHc K (m ℓ) n :=
  extensionCohomologyEquiv ℓ (affineOpen K) n

private def punctureCoefficients (n : ℕ) :
    punctureHc K (M ℓ) n ≃+ punctureHc K (m ℓ) n :=
  extensionCohomologyEquiv ℓ ((cuspPuncturedOpen K).ι ≫ affineOpen K) n

private def zmodLinearEquiv {B C : Type} [AddCommGroup B] [AddCommGroup C]
    [Module (ZMod ℓ) B] [Module (ZMod ℓ) C] (e : B ≃+ C) : B ≃ₗ[ZMod ℓ] C where
  toAddEquiv := e
  map_smul' r x := by
    letI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    change e (r • x) = r • e x
    have h : (r.val : ZMod ℓ) = r := ZMod.natCast_zmod_val r
    rw [← h, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

private theorem finrank_eq_zero_of_addEquiv_to_subsingleton {B C : Type}
    [AddCommGroup B] [AddCommGroup C] [Module (ZMod ℓ) B]
    (e : B ≃+ C) (h : Subsingleton C) : Module.finrank (ZMod ℓ) B = 0 := by
  letI : Subsingleton B := ⟨fun a b => e.injective (h.elim _ _)⟩
  exact Module.finrank_zero_of_subsingleton

private theorem finrank_eq_one_of_addEquiv {B : Type} [AddCommGroup B] [Module (ZMod ℓ) B]
    (e : B ≃+ ZMod ℓ) : Module.finrank (ZMod ℓ) B = 1 :=
  (LinearEquiv.finrank_eq (zmodLinearEquiv ℓ e)).trans (Module.finrank_self _)

include kClosed p pPrime pChar coeffNZ

theorem cusp_finrank_zero : Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) 0) = 0 := by
  exact finrank_eq_zero_of_addEquiv_to_subsingleton ℓ (cuspCoefficients K ℓ 0)
    (compactSupportHZero_subsingleton K (m ℓ)).2

theorem puncture_finrank_zero : Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) 0) = 0 := by
  exact finrank_eq_zero_of_addEquiv_to_subsingleton ℓ (punctureCoefficients K ℓ 0)
    (compactSupportHZero_subsingleton K (m ℓ)).1

theorem cusp_finrank_one : Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) 1) = 0 :=
  finrank_eq_zero_of_addEquiv_to_subsingleton ℓ (cuspCoefficients K ℓ 1)
    (CuspCompactSupportAbsoluteHOne.cuspHcOne_subsingleton K p ℓ)

theorem puncture_finrank_one : Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) 1) = 1 :=
  finrank_eq_one_of_addEquiv ℓ ((punctureCoefficients K ℓ 1).trans
    (CuspCompactSupportAbsoluteHOne.punctureHcOneEquiv K p ℓ))

theorem cusp_finrank_two : Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) 2) = 1 := by
  obtain ⟨e⟩ := CuspCompactSupportDegreeTwo.nonempty_cuspHcTwoEquiv K p ℓ
    (Fact.out : ℓ.Prime).two_le
  exact finrank_eq_one_of_addEquiv ℓ ((cuspCoefficients K ℓ 2).trans e)

theorem puncture_finrank_two : Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) 2) = 1 := by
  obtain ⟨e⟩ := CuspCompactSupportDegreeTwo.nonempty_punctureHcTwoEquiv K p ℓ
    (Fact.out : ℓ.Prime).two_le
  exact finrank_eq_one_of_addEquiv ℓ ((punctureCoefficients K ℓ 2).trans e)

theorem cusp_finrank_add_three (n : ℕ) :
    Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) (n + 3)) = 0 :=
  finrank_eq_zero_of_addEquiv_to_subsingleton ℓ (cuspCoefficients K ℓ (n + 3))
    (CuspCompactSupportAllHigher.cuspHc_add_three_subsingleton K p ℓ n)

theorem puncture_finrank_add_three (n : ℕ) :
    Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) (n + 3)) = 0 :=
  finrank_eq_zero_of_addEquiv_to_subsingleton ℓ (punctureCoefficients K ℓ (n + 3))
    (CuspCompactSupportAllHigher.punctureHc_add_three_subsingleton K p ℓ n)

/-- The alternating sum over every degree through N−1. -/
def eulerThrough (d : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (d n : ℤ)

private theorem eulerThrough_eq_three (d : ℕ → ℕ) (hTail : ∀ n, d (n + 3) = 0)
    (N : ℕ) (hN : 3 ≤ N) : eulerThrough d N = eulerThrough d 3 := by
  unfold eulerThrough
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i _ hi
  have h : 3 ≤ i := Nat.le_of_not_gt (fun hh => hi (Finset.mem_range.mpr hh))
  have e : i = (i - 3) + 3 := by omega
  have hd : d i = 0 := by rw [e, hTail]
  simp [hd]

/-- All common truncations containing degrees zero, one and two give the
individual compact Euler sums of the two actual curves. -/
theorem complete_euler_sums (N : ℕ) (hN : 3 ≤ N) :
    eulerThrough (fun n => Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) n)) N = 1 ∧
    eulerThrough (fun n => Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) n)) N = 0 := by
  constructor
  · rw [eulerThrough_eq_three _ (cusp_finrank_add_three K p ℓ) N hN]
    norm_num [eulerThrough, Finset.sum_range_succ, cusp_finrank_zero K p ℓ,
      cusp_finrank_one K p ℓ, cusp_finrank_two K p ℓ]
  · rw [eulerThrough_eq_three _ (puncture_finrank_add_three K p ℓ) N hN]
    norm_num [eulerThrough, Finset.sum_range_succ, puncture_finrank_zero K p ℓ,
      puncture_finrank_one K p ℓ, puncture_finrank_two K p ℓ]

end
end ManuscriptAudit.CuspFiniteCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspFiniteCohomology.cusp_finrank_zero,
      ``ManuscriptAudit.CuspFiniteCohomology.puncture_finrank_zero,
      ``ManuscriptAudit.CuspFiniteCohomology.cusp_finrank_one,
      ``ManuscriptAudit.CuspFiniteCohomology.puncture_finrank_one,
      ``ManuscriptAudit.CuspFiniteCohomology.cusp_finrank_two,
      ``ManuscriptAudit.CuspFiniteCohomology.puncture_finrank_two,
      ``ManuscriptAudit.CuspFiniteCohomology.cusp_finrank_add_three,
      ``ManuscriptAudit.CuspFiniteCohomology.puncture_finrank_add_three,
      ``ManuscriptAudit.CuspFiniteCohomology.complete_euler_sums] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
