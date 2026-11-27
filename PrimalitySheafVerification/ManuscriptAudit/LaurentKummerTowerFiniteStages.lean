import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentKummerTowerAlgebra

/-! Actual finite Laurent stages form an increasing union in the
algebra carrying all Laurent-coordinate roots. -/

namespace ManuscriptAudit.LaurentKummerTowerFiniteStages

open LaurentKummerTowerAlgebra (Exponent Tower rootExponent rootExponent_succ exponent_from_finite_stage)

noncomputable section

variable (K : Type*) [CommRing K] (ℓ : ℕ)

/-- The exponent map of the actual stage. -/
def stageExponent (n : ℕ) : ℤ →+ Exponent ℓ where
  toFun z := z • rootExponent ℓ n
  map_zero' := zero_smul ℤ _
  map_add' a b := add_smul a b _

/-- The finite Laurent stage embeds its coordinate as the chosen power root. -/
def stageMap (n : ℕ) : LaurentPolynomial K →+* Tower K ℓ :=
  AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ n)

private def linkExponent : ℤ →+ ℤ where
  toFun z := ℓ • z
  map_zero' := smul_zero ℓ
  map_add' a b := smul_add ℓ a b

/-- From one finite Laurent stage to the next, use the power of its coordinate. -/
def link : LaurentPolynomial K →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapDomainRingHom K (linkExponent ℓ)

private theorem stageExponent_comp (n : ℕ) :
    (stageExponent ℓ (n + 1)).comp (linkExponent ℓ) = stageExponent ℓ n := by
  ext z
  change (ℓ • z) • rootExponent ℓ (n + 1) = z • rootExponent ℓ n
  rw [smul_assoc, smul_comm ℓ z, rootExponent_succ]

theorem stageMap_comp_link (n : ℕ) :
    (stageMap K ℓ (n + 1)).comp (link K ℓ) = stageMap K ℓ n := by
  change (AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ (n + 1))).comp
      (AddMonoidAlgebra.mapDomainRingHom K (linkExponent ℓ)) =
    AddMonoidAlgebra.mapDomainRingHom K (stageExponent ℓ n)
  rw [← AddMonoidAlgebra.mapDomainRingHom_comp, stageExponent_comp]

abbrev stage (n : ℕ) : Subring (Tower K ℓ) := (stageMap K ℓ n).range

theorem stage_mono : Monotone (stage K ℓ) :=
  monotone_nat_of_le_succ (fun n x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨link K ℓ y, ?_⟩
    exact RingHom.congr_fun (stageMap_comp_link K ℓ n) y)

private theorem stage_single (n : ℕ) (z : ℤ) (a : K) :
    stageMap K ℓ n (AddMonoidAlgebra.single z a) = AddMonoidAlgebra.single (stageExponent ℓ n z) a :=
  AddMonoidAlgebra.mapDomain_single _ _ _

/-- Every element, including arbitrary finite linear combinations of monomials,
is in the image of a single actual finite Laurent stage. -/
theorem exists_stage (v : Tower K ℓ) : ∃ n : ℕ, ∃ u : LaurentPolynomial K, stageMap K ℓ n u = v := by
  let S := ⨆ n, stage K ℓ n
  have hScalar (a : K) : algebraMap K (Tower K ℓ) a ∈ S := by
    apply (le_iSup (stage K ℓ) 0)
    refine ⟨AddMonoidAlgebra.single 0 a, ?_⟩
    rw [stage_single, map_zero]
    rfl
  have hV : v ∈ S := by
    apply AddMonoidAlgebra.induction_on v
    · intro x
      obtain ⟨n, z, hz⟩ := exponent_from_finite_stage ℓ x
      apply (le_iSup (stage K ℓ) n)
      refine ⟨AddMonoidAlgebra.single z 1, ?_⟩
      rw [stage_single, AddMonoidAlgebra.of_apply]
      exact congrArg (fun y : Exponent ℓ ↦ AddMonoidAlgebra.single y (1 : K)) hz
    · intro a b ha hb
      exact S.add_mem ha hb
    · intro a v hv
      rw [Algebra.smul_def]
      exact S.mul_mem (hScalar a) hv
  have hdir : Directed (· ≤ ·) (stage K ℓ) := (stage_mono K ℓ).directed_le
  exact (Subring.mem_iSup_of_directed _ hdir).mp hV

end
end ManuscriptAudit.LaurentKummerTowerFiniteStages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentKummerTowerFiniteStages.stageMap_comp_link,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.stage_mono,
      ``ManuscriptAudit.LaurentKummerTowerFiniteStages.exists_stage] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
