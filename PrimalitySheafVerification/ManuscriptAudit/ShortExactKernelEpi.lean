import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.Refinements

/-! The map between the right kernels in a diagram of short exact rows
is epic when the left vertical arrow is epic. -/

namespace ManuscriptAudit.ShortExactKernelEpi

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

noncomputable section

variable {C : Type*} [Category C] [Abelian C]
variable {S T K : ShortComplex C}
variable (v : S ⟶ T) (i : K ⟶ S)
variable {h₂ : i.τ₂ ≫ v.τ₂ = 0} {h₃ : i.τ₃ ≫ v.τ₃ = 0}

/-- The cokernel of the left vertical arrow is the only obstruction
to epimorphy between the right kernels. -/
theorem epi_right (hT : T.Exact) [Epi S.g] [Epi v.τ₁]
    (k₂ : IsLimit (KernelFork.ofι i.τ₂ h₂))
    (k₃ : IsLimit (KernelFork.ofι i.τ₃ h₃)) : Epi K.g := by
  apply (epi_iff_surjective_up_to_refinements K.g).2
  intro A a
  obtain ⟨B, e, he, b, hb⟩ :=
    surjective_up_to_refinements_of_epi S.g (a ≫ i.τ₃)
  have hbg : (b ≫ v.τ₂) ≫ T.g = 0 := by
    calc
      _ = (b ≫ S.g) ≫ v.τ₃ := by
        rw [Category.assoc, v.comm₂₃, ← Category.assoc]
      _ = 0 := by rw [← hb, Category.assoc, Category.assoc, h₃, comp_zero, comp_zero]
  obtain ⟨D, f, hf, c, hc⟩ := hT.exact_up_to_refinements (b ≫ v.τ₂) hbg
  obtain ⟨E, g, hg, d, hd⟩ := surjective_up_to_refinements_of_epi v.τ₁ c
  let w := (g ≫ f ≫ b) - d ≫ S.f
  have hw : w ≫ v.τ₂ = 0 := by
    have hleft : (g ≫ f ≫ b) ≫ v.τ₂ = d ≫ v.τ₁ ≫ T.f := by
      calc
        _ = g ≫ (f ≫ b ≫ v.τ₂) := by simp only [Category.assoc]
        _ = _ := by rw [← Category.assoc f b v.τ₂, hc, ← Category.assoc g c T.f, hd]
    rw [sub_comp, hleft, v.comm₁₂, Category.assoc, sub_self]
  let k := k₂.lift (KernelFork.ofι w hw)
  have hk : k ≫ i.τ₂ = w := k₂.fac (KernelFork.ofι w hw) WalkingParallelPair.zero
  letI : Mono i.τ₃ := mono_of_isLimit_fork k₃
  refine ⟨E, g ≫ f ≫ e, inferInstance, k, ?_⟩
  apply (cancel_mono i.τ₃).mp
  calc
    _ = (g ≫ f ≫ b) ≫ S.g := by
      simp only [Category.assoc, hb]
    _ = w ≫ S.g := by
      simp only [w, sub_comp, Category.assoc, S.zero, comp_zero, sub_zero]
    _ = _ := by rw [← hk, Category.assoc, i.comm₂₃, ← Category.assoc]

end
end ManuscriptAudit.ShortExactKernelEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ShortExactKernelEpi.epi_right
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
