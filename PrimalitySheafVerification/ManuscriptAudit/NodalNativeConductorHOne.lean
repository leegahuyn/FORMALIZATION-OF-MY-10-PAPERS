import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedProetaleHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! The conductor map describes actual native degree-one cohomology
with every invertible cyclic coefficient order. -/

namespace ManuscriptAudit.NodalNativeConductorHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalProetaleConductorSequence (sequence sequence_shortExact)
open NodalProetaleConductorHZero (originHZeroEquiv difference_HZero_eq_zero)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteConstant (constantIso nativeResidueIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

private abbrev J := Scheme.ProEt.topology (projectiveNode K)
private abbrev G := AddCommGrpCat.{1}
private abbrev I := (constantSheaf (J K) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))

section Discrete

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

/-- The conductor label maps to native H¹ by the actual normalization exact sequence. -/
def boundary : M →+ Sheaf.H (functions M (projectiveNode K)) 1 :=
  ((sequence_shortExact K h2 M).extClass.postcomp (I K) (show 0 + 1 = 1 by rfl)).comp
    (originHZeroEquiv K M).symm.toAddMonoidHom

theorem boundary_injective : Function.Injective (boundary K h2 M) := by
  let S := sequence K h2 M
  let hS := sequence_shortExact K h2 M
  let δ : Sheaf.H S.X₃ 0 →+ Sheaf.H S.X₁ 1 := hS.extClass.postcomp (I K) rfl
  have hδ : Function.Injective δ := by
    have hz (x : Sheaf.H S.X₃ 0) (hx : δ x = 0) : x = 0 := by
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ (I K) hS x rfl hx
      change Sheaf.H.map (sequence K h2 M).g 0 y = x at hy
      rw [difference_HZero_eq_zero K M h2] at hy
      exact hy.symm
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hab, sub_self]
  exact hδ.comp (originHZeroEquiv K M).symm.injective

theorem boundary_surjective
    (h : Subsingleton (Sheaf.H (functions M (normalizedNode K)) 1)) :
    Function.Surjective (boundary K h2 M) := by
  let S := sequence K h2 M
  let hS := sequence_shortExact K h2 M
  letI := h
  let hN : Subsingleton (Sheaf.H S.X₂ 1) :=
    ProetaleDirectImageHOne.directImage_HOne_subsingleton (normalizationMap K) (functions M (normalizedNode K))
  intro x
  have hx : Sheaf.H.map S.f 1 x = 0 := hN.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ (I K) hS x hx rfl
  refine ⟨originHZeroEquiv K M c, ?_⟩
  change (hS.extClass.postcomp (I K) (show 0 + 1 = 1 by rfl))
    ((originHZeroEquiv K M).symm (originHZeroEquiv K M c)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hc

end Discrete

variable [IsAlgClosed K]

local instance cyclicTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- Native degree-one cohomology of the actual proper split node is one
copy of the cyclic coefficient group, for every positive invertible order. -/
def cyclicHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (J K) G).obj (AddCommGrpCat.of (ULift.{1} (ZMod d)))) 1 ≃+ ZMod d := by
  let e := cohomologyIso (X := normalizedNode K) (constantIso (normalizedNode K) (ZMod d)) 1
  let h := NodalNormalizedProetaleHOne.cyclic_HOne_subsingleton K h2 d
  have hN : Subsingleton (Sheaf.H (functions (ZMod d) (normalizedNode K)) 1) :=
    ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩
  let b := AddEquiv.ofBijective (boundary K h2 (ZMod d))
    ⟨boundary_injective K h2 (ZMod d), boundary_surjective K h2 (ZMod d) hN⟩
  exact (cohomologyIso (X := projectiveNode K) (constantIso (projectiveNode K) (ZMod d)) 1).trans b.symm

/-- The same computation for the literal finite coefficient of the native ℓ-adic tower. -/
def residueHOneEquiv (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] (n : ℕ) :
    Sheaf.H (ProetaleAdicHOneDetection.finiteCoefficient (projectiveNode K) ℓ n) 1 ≃+ ZMod (ℓ ^ n) := by
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  exact (cohomologyIso (X := projectiveNode K) (nativeResidueIso (projectiveNode K) ℓ n) 1).symm.trans
    (cyclicHOneEquiv K h2 (ℓ ^ n))

end
end ManuscriptAudit.NodalNativeConductorHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeConductorHOne.boundary_injective,
      ``ManuscriptAudit.NodalNativeConductorHOne.boundary_surjective,
      ``ManuscriptAudit.NodalNativeConductorHOne.cyclicHOneEquiv,
      ``ManuscriptAudit.NodalNativeConductorHOne.residueHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
