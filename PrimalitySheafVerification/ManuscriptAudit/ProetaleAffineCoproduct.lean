import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! A finite jointly surjective affine family in the native pro-étale
site gives a single flat affine cover via the actual scheme coproduct. -/

namespace ManuscriptAudit.ProetaleAffineCoproduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {T : S.ProEt} {n : ℕ}
  (V : Fin n → S.ProEt)

private abbrev pieces : Fin n → Scheme.{u} := fun i ↦ (V i).left

/-- The actual disjoint union of weakly étale objects. -/
def coproduct : S.ProEt :=
  let f : (∐ pieces V) ⟶ S := Sigma.desc (fun i ↦ (V i).hom)
  haveI : WeaklyEtale f := IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale)
    (fun i ↦ inferInstanceAs (WeaklyEtale (V i).hom))
  Scheme.ProEt.mk f

/-- The actual coproduct injection over the base scheme. -/
def injection (i : Fin n) : V i ⟶ coproduct V :=
  MorphismProperty.Over.homMk (Sigma.ι (pieces V) i) (Sigma.ι_desc _ _)

instance [∀ i, IsAffine (V i).left] : IsAffine (coproduct V).left := by
  change IsAffine (∐ pieces V)
  infer_instance

variable (a : ∀ i, V i ⟶ T)

/-- Combine the maps from each component using the native coproduct. -/
def descent : coproduct V ⟶ T :=
  MorphismProperty.Over.homMk (Sigma.desc (fun i ↦ (a i).left)) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (pieces V) i ≫ Sigma.desc (fun k ↦ (a k).left) ≫ T.hom =
      Sigma.ι (pieces V) i ≫ Sigma.desc (fun k ↦ (V k).hom)
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact MorphismProperty.Over.w (a i))

theorem injection_descent (i : Fin n) : injection V i ≫ descent V a = a i := by
  apply (Scheme.ProEt.forget S ⋙ Over.forget S).map_injective
  exact Sigma.ι_desc _ _

theorem descent_weaklyEtale (ha : ∀ i, WeaklyEtale (a i).left) :
    WeaklyEtale (descent V a).left :=
  IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) ha

theorem descent_surjective
    (ha : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x) :
    Surjective (descent V a).left := by
  constructor
  intro x
  obtain ⟨i, y, hy⟩ := ha x
  refine ⟨(injection V i).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  have h : (injection V i).left ≫ (descent V a).left = (a i).left :=
    congrArg (fun f : V i ⟶ T => f.left) (injection_descent V a i)
  rwa [h]

/-- The combined arrow is a covering singleton in the actual pro-étale
topology. The target and all components are affine. -/
theorem descent_covers [IsAffine T.left] [∀ i, IsAffine (V i).left]
    (hWeak : ∀ i, WeaklyEtale (a i).left)
    (hSurj : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x) :
    Sieve.generate (Presieve.singleton (descent V a)) ∈ Scheme.ProEt.topology S T := by
  let f := descent V a
  letI : Surjective f.left := descent_surjective V a hSurj
  letI : QuasiCompact f.left := inferInstance
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.singleton f).map (Scheme.ProEt.forget S ⋙ Over.forget S) ∈
    Scheme.proetalePrecoverage T.left
  rw [Presieve.map_singleton]
  change Presieve.singleton f.left ∈ Scheme.propQCPrecoverage @WeaklyEtale T.left
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (descent_weaklyEtale V a hWeak)

end
end ManuscriptAudit.ProetaleAffineCoproduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineCoproduct.injection_descent,
      ``ManuscriptAudit.ProetaleAffineCoproduct.descent_weaklyEtale,
      ``ManuscriptAudit.ProetaleAffineCoproduct.descent_covers] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
