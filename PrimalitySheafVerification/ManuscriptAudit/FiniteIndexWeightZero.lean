import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.Topology.Separation.Connected
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexWeightZeroCosets

/-!
# Finite-index weight-zero constancy

For each scalar c, the product of all coset translates of f-c descends
to a level-one weight-zero modular form. Its constancy implies that f
has finite image. Continuity and connectedness then give constancy.
-/

namespace ManuscriptAudit.FiniteIndexWeightZero

open Set Filter UpperHalfPlane ModularForm
open FiniteIndexWeightZeroCosets
open scoped MatrixGroups Manifold ModularForm

noncomputable section

private theorem holomorphic_finset_product {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (hF : ∀ j : ι, MDiff (F j)) :
    MDiff (fun z : ℍ => ∏ j ∈ s, F j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
  | @insert j s hjs ih =>
      simpa only [Finset.prod_insert hjs, Pi.mul_def] using (hF j).mul ih

private theorem bounded_finset_product {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (hF : ∀ j : ι, IsBoundedAtImInfty (F j)) :
    IsBoundedAtImInfty (fun z : ℍ => ∏ j ∈ s, F j z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      change BoundedAtFilter atImInfty (Function.const ℍ (1 : ℂ))
      exact const_boundedAtFilter atImInfty 1
  | @insert j s hjs ih =>
      simpa only [Finset.prod_insert hjs, Pi.mul_def, IsBoundedAtImInfty] using (hF j).mul ih

private theorem cosetProduct_holomorphic (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (f : ℍ → ℂ) (hf : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, f (g • z) = f z)
    (hHol : MDiff f) (c : ℂ) : MDiff (cosetProduct H f hf c) := by
  letI := rightCosetFintype H
  unfold cosetProduct
  refine holomorphic_finset_product Finset.univ _ (fun q => ?_)
  refine Quotient.inductionOn q (fun g => ?_)
  change MDiff (fun z : ℍ => f (g • z) - c)
  have hSl := hHol.slash (0 : ℤ) (g : GL (Fin 2) ℝ)
  change MDiff (f ∣[(0 : ℤ)] g) at hSl
  have ht : MDiff (fun z : ℍ => f (g • z)) := by
    simpa [SL_slash_def] using hSl
  exact ht.sub mdifferentiable_const

private theorem cosetProduct_bounded (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (f : ℍ → ℂ) (hf : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, f (g • z) = f z)
    (hInfinity : ∀ g : SL(2, ℤ), IsBoundedAtImInfty (fun z : ℍ => f (g • z)))
    (c : ℂ) : IsBoundedAtImInfty (cosetProduct H f hf c) := by
  letI := rightCosetFintype H
  unfold cosetProduct
  refine bounded_finset_product Finset.univ _ (fun q => ?_)
  refine Quotient.inductionOn q (fun g => ?_)
  change IsBoundedAtImInfty (fun z : ℍ => f (g • z) - c)
  exact (hInfinity g).sub (const_boundedAtFilter atImInfty c)

private theorem cosetProduct_slash (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (f : ℍ → ℂ) (hf : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, f (g • z) = f z)
    (c : ℂ) (g : SL(2, ℤ)) :
    cosetProduct H f hf c ∣[(0 : ℤ)] g = cosetProduct H f hf c := by
  funext z
  simp only [SL_slash_def, neg_zero, zpow_zero, mul_one]
  change cosetProduct H f hf c (g • z) = cosetProduct H f hf c z
  exact cosetProduct_smul H f hf c g z

private def cosetModularForm (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (f : ℍ → ℂ) (hf : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, f (g • z) = f z)
    (hHol : MDiff f)
    (hInfinity : ∀ g : SL(2, ℤ), IsBoundedAtImInfty (fun z : ℍ => f (g • z))) (c : ℂ) :
    ModularForm 𝒮ℒ 0 where
  toFun := cosetProduct H f hf c
  slash_action_eq' A hA := by
    obtain ⟨g, rfl⟩ := hA
    change cosetProduct H f hf c ∣[(0 : ℤ)] g = cosetProduct H f hf c
    exact cosetProduct_slash H f hf c g
  holo' := cosetProduct_holomorphic H f hf hHol c
  bdd_at_cusps' hc := by
    apply (OnePoint.isBoundedAt_iff_exists_SL2Z hc).2
    obtain ⟨g, hg⟩ := isCusp_SL2Z_iff'.mp hc
    refine ⟨g, hg.symm, ?_⟩
    change IsBoundedAtImInfty (cosetProduct H f hf c ∣[(0 : ℤ)] g)
    rw [cosetProduct_slash]
    exact cosetProduct_bounded H f hf hInfinity c

theorem weight_zero_eq_const (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, f (g • z) = f z)
    (hHol : MDiff f)
    (hInfinity : ∀ g : SL(2, ℤ), IsBoundedAtImInfty (fun z : ℍ => f (g • z))) :
    ∃ c : ℂ, f = Function.const ℍ c := by
  have hConst (c : ℂ) (z w : ℍ) : cosetProduct H f hf c z = cosetProduct H f hf c w := by
    let F := cosetModularForm H f hf hHol hInfinity c
    obtain ⟨a, ha⟩ := ModularFormClass.levelOne_weight_zero_const F
    exact (congrFun ha z).trans (congrFun ha w).symm
  have hFinite := finite_image_of_constant_coset_products H f hf hConst
  have hPre := isPreconnected_range hHol.continuous
  have hSub : (Set.range f).Subsingleton := by
    by_contra h
    exact hFinite.not_infinite (hPre.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  let z₀ : ℍ := ⟨Complex.I, by simp⟩
  exact ⟨f z₀, funext (fun z => hSub (Set.mem_range_self z) (Set.mem_range_self z₀))⟩

end
end ManuscriptAudit.FiniteIndexWeightZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FiniteIndexWeightZero.weight_zero_eq_const
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
