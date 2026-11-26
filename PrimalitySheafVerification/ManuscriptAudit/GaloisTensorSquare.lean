import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Pi
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The tensor square of a finite Galois extension

The projection indexed by an automorphism sends a simple tensor
to the product of the left entry with the automorphism applied to
the right entry. Pairwise separating tensors give the coordinate
vectors, and the Galois degree formula gives equal dimensions.
-/

namespace ManuscriptAudit.GaloisTensorSquare

open scoped TensorProduct BigOperators

noncomputable section

variable (F L : Type*) [Field F] [Field L] [Algebra F L]

/-- The native Galois evaluation from the tensor square to the product. -/
def evaluationHom : L ⊗[F] L →ₐ[L] ((L ≃ₐ[F] L) → L) :=
  AlgHom.pi fun σ ↦ Algebra.TensorProduct.lift (AlgHom.id L L) σ.toAlgHom
    (fun x y ↦ Commute.all x (σ y))

@[simp] theorem evaluationHom_tmul (x y : L) (σ : L ≃ₐ[F] L) :
    evaluationHom F L (x ⊗ₜ[F] y) σ = x * σ y := rfl

private theorem exists_separator (σ τ : L ≃ₐ[F] L) (h : σ ≠ τ) :
    ∃ w : L ⊗[F] L, evaluationHom F L w σ = 1 ∧ evaluationHom F L w τ = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : L, σ x ≠ τ x := by
    by_contra! he
    exact h (AlgEquiv.ext he)
  let w : L ⊗[F] L :=
    (σ x - τ x)⁻¹ • ((1 : L) ⊗ₜ[F] x - (τ x) ⊗ₜ[F] (1 : L))
  refine ⟨w, ?_, ?_⟩
  · simp [w, smul_eq_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hx)]
  · simp [w]

variable [FiniteDimensional F L]

private theorem exists_coordinate (σ : L ≃ₐ[F] L) :
    ∃ w : L ⊗[F] L, ∀ τ : L ≃ₐ[F] L,
      evaluationHom F L w τ = if τ = σ then 1 else 0 := by
  classical
  letI := Fintype.ofFinite (L ≃ₐ[F] L)
  let c (τ : L ≃ₐ[F] L) : L ⊗[F] L :=
    if h : σ ≠ τ then Classical.choose (exists_separator F L σ τ h) else 1
  have hσ (τ : L ≃ₐ[F] L) (h : τ ≠ σ) : evaluationHom F L (c τ) σ = 1 := by
    simpa only [c, dif_pos (Ne.symm h)] using
      (Classical.choose_spec (exists_separator F L σ τ h.symm)).1
  have hτ (τ : L ≃ₐ[F] L) (h : τ ≠ σ) : evaluationHom F L (c τ) τ = 0 := by
    simpa only [c, dif_pos (Ne.symm h)] using
      (Classical.choose_spec (exists_separator F L σ τ h.symm)).2
  let s := Finset.univ.erase σ
  let w := ∏ τ ∈ s, c τ
  have hprod (τ : L ≃ₐ[F] L) :
      evaluationHom F L w τ = ∏ ρ ∈ s, evaluationHom F L (c ρ) τ := by
    exact map_prod ((Pi.evalAlgHom L (fun _ : L ≃ₐ[F] L ↦ L) τ).comp (evaluationHom F L)) c s
  refine ⟨w, fun τ ↦ ?_⟩
  rw [hprod]
  by_cases h : τ = σ
  · subst τ
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun ρ hρ ↦ hσ ρ (Finset.mem_erase.mp hρ).1)
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ τ⟩) (hτ τ h)

/-- The evaluation projections of the tensor square are jointly surjective
onto the finite product. -/
theorem evaluationHom_surjective : Function.Surjective (evaluationHom F L) := by
  classical
  letI := Fintype.ofFinite (L ≃ₐ[F] L)
  choose w hw using exists_coordinate F L
  intro f
  refine ⟨∑ σ : L ≃ₐ[F] L, f σ • w σ, ?_⟩
  funext τ
  let p := (Pi.evalAlgHom L (fun _ : L ≃ₐ[F] L ↦ L) τ).comp (evaluationHom F L)
  change p (∑ σ : L ≃ₐ[F] L, f σ • w σ) = f τ
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ σ : L ≃ₐ[F] L, f σ * evaluationHom F L (w σ) τ) = f τ
  simp only [hw]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro σ _ h
    simp [h.symm]
  · simp

variable [IsGalois F L]

/-- The tensor square splits as one copy of the extension for each
Galois automorphism, with the displayed native coordinate maps. -/
def tensorProductEquiv : L ⊗[F] L ≃ₐ[L] ((L ≃ₐ[F] L) → L) := by
  classical
  letI := Fintype.ofFinite (L ≃ₐ[F] L)
  have hdim : Module.finrank L (L ⊗[F] L) = Module.finrank L ((L ≃ₐ[F] L) → L) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  have hsurj := evaluationHom_surjective F L
  have hinj : Function.Injective (evaluationHom F L) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (evaluationHom F L).toLinearMap)).mpr hsurj
  exact AlgEquiv.ofBijective (evaluationHom F L) ⟨hinj, hsurj⟩

@[simp] theorem tensorProductEquiv_tmul (x y : L) (σ : L ≃ₐ[F] L) :
    tensorProductEquiv F L (x ⊗ₜ[F] y) σ = x * σ y :=
  evaluationHom_tmul F L x y σ

end

end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisTensorSquare.evaluationHom_tmul,
      ``ManuscriptAudit.GaloisTensorSquare.evaluationHom_surjective,
      ``ManuscriptAudit.GaloisTensorSquare.tensorProductEquiv,
      ``ManuscriptAudit.GaloisTensorSquare.tensorProductEquiv_tmul] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
