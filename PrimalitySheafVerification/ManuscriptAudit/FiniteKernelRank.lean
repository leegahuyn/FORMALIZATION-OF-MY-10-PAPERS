import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rank of a surjection with finite-dimensional kernel

A vector space splits into the kernel and target of a surjection after
choosing a linear section. Finite dimensionality of the kernel and
target suffices for the dimension formula.
-/

namespace ManuscriptAudit.FiniteKernelRank

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- Choose a linear section of a surjective map and split off its actual kernel. -/
noncomputable def kernelProductEquiv (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    V ≃ₗ[K] (f.ker × W) := by
  let hs := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  let g := Classical.choose hs
  have hg (y : W) : f (g y) = y := LinearMap.congr_fun (Classical.choose_spec hs) y
  let d : V →ₗ[K] V := LinearMap.id - g.comp f
  have hd (x : V) : d x ∈ f.ker := by
    change f (x - g (f x)) = 0
    rw [map_sub, hg, sub_self]
  let t : V →ₗ[K] (f.ker × W) := (d.codRestrict f.ker hd).prod f
  refine LinearEquiv.ofBijective t ⟨?_, ?_⟩
  · intro a b h
    have hmap : f a = f b := congrArg Prod.snd h
    have hker : a - g (f a) = b - g (f b) :=
      congrArg (fun z : f.ker × W => (z.1 : V)) h
    rw [hmap] at hker
    exact sub_right_inj.mp hker
  · rintro ⟨a, b⟩
    have hab : f ((a : V) + g b) = b := by
      rw [map_add, show f (a : V) = 0 from a.property, zero_add, hg]
    refine ⟨(a : V) + g b, Prod.ext (Subtype.ext ?_) hab⟩
    change (a : V) + g b - g (f ((a : V) + g b)) = (a : V)
    rw [hab, add_sub_cancel_right]

/-- Only the kernel and target need to be known finite-dimensional. -/
theorem finiteDimensional_and_finrank (f : V →ₗ[K] W) (hf : Function.Surjective f)
    [FiniteDimensional K f.ker] [FiniteDimensional K W] :
    FiniteDimensional K V ∧ Module.finrank K V = Module.finrank K f.ker + Module.finrank K W := by
  let e := kernelProductEquiv f hf
  exact ⟨e.symm.finiteDimensional, e.finrank_eq.trans Module.finrank_prod⟩

end ManuscriptAudit.FiniteKernelRank

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteKernelRank.kernelProductEquiv,
      ``ManuscriptAudit.FiniteKernelRank.finiteDimensional_and_finrank] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
