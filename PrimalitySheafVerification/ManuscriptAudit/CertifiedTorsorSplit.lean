import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Pi
import PrimalitySheafVerification.ManuscriptAudit.InvolutionTensorBaseChange

/-!
# Splitting a certified two-sheet cover after a section

Given an algebra map from the cover to a base algebra, extension to
that algebra identifies the two-copy comparison with the two
components indexed by the original deck involution.
-/

namespace ManuscriptAudit.CertifiedTorsorSplit

open InvolutionTensorComparison InvolutionTensorBaseChange
open scoped TensorProduct

noncomputable section

variable (A E B : Type*) [CommRing A] [CommRing E] [CommRing B]
  [Algebra A E] [Algebra A B] [Algebra E B] [IsScalarTower A E B]

local instance : IsScalarTower E B B := IsScalarTower.right

variable (σ : E ≃ₐ[A] E) (c : CertifiedComparison A E σ)

/-- The affine splitting associated to an actual section of the cover. -/
def split : B ⊗[A] E ≃ₐ[B] B × B :=
  (Algebra.TensorProduct.cancelBaseChange A E B B E).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) c.equiv).trans
      ((Algebra.TensorProduct.prodRight E B B E E).trans
        (AlgEquiv.prodCongr (Algebra.TensorProduct.rid E B B) (Algebra.TensorProduct.rid E B B))))

theorem split_tmul (b : B) (e : E) :
    split A E B σ c (b ⊗ₜ[A] e) =
      (algebraMap E B e * b, algebraMap E B (σ e) * b) := by
  simp only [split, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply]
  change (Algebra.TensorProduct.rid E B B (b ⊗ₜ[E] (c.equiv (1 ⊗ₜ[A] e)).1),
    Algebra.TensorProduct.rid E B B (b ⊗ₜ[E] (c.equiv (1 ⊗ₜ[A] e)).2)) = _
  rw [c.on_tmul]
  simp [Algebra.smul_def]

theorem split_deck (hσ : Function.Involutive σ) (z : B ⊗[A] E) :
    split A E B σ c (baseSwap A E B σ z) = (split A E B σ c z).swap := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp only [baseSwap_tmul, split_tmul, hσ e] <;> rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy] <;> rfl

def firstIdempotent : B ⊗[A] E := (split A E B σ c).symm (1, 0)

def secondIdempotent : B ⊗[A] E := (split A E B σ c).symm (0, 1)

theorem idempotents_mul :
    firstIdempotent A E B σ c * secondIdempotent A E B σ c = 0 := by
  apply (split A E B σ c).injective
  simp [firstIdempotent, secondIdempotent]

theorem idempotents_add :
    firstIdempotent A E B σ c + secondIdempotent A E B σ c = 1 := by
  apply (split A E B σ c).injective
  simp [firstIdempotent, secondIdempotent]

theorem deck_firstIdempotent (hσ : Function.Involutive σ) :
    baseSwap A E B σ (firstIdempotent A E B σ c) = secondIdempotent A E B σ c := by
  apply (split A E B σ c).injective
  rw [split_deck A E B σ c hσ]
  simp [firstIdempotent, secondIdempotent]

end

end ManuscriptAudit.CertifiedTorsorSplit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.CertifiedTorsorSplit.split_tmul,
      ``ManuscriptAudit.CertifiedTorsorSplit.split_deck,
      ``ManuscriptAudit.CertifiedTorsorSplit.idempotents_mul,
      ``ManuscriptAudit.CertifiedTorsorSplit.idempotents_add,
      ``ManuscriptAudit.CertifiedTorsorSplit.deck_firstIdempotent] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
