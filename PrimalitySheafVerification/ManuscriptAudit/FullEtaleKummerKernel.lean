import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerHOne
import PrimalitySheafVerification.ManuscriptAudit.AffineKummerTorsionTransition

/-! The actual full étale Kummer kernels form a tower under the literal
root power maps. Their images in unit cohomology have the same transitions. -/

namespace ManuscriptAudit.FullEtaleKummerKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open KummerUnitsSheaf KummerCohomologyDegreeTwo
open KummerSheafSequence (unitSheaf)
open FullEtaleKummerHOne AffineKummerTorsionTransition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0})

private abbrev C := AddCommGrpCat.{0}
private abbrev Q := (Scheme.AffineEtale.sheafEquiv X C).functor
private abbrev p := KummerSheafSequence.sheafPower X
private abbrev S := KummerRelativeFull.sequence X

/-- The literal full unit sheaf used in the Kummer short complex. -/
abbrev U := (Q X).obj (unitSheaf X)

private theorem p_eq (d : ℕ) : p X d = d • 𝟙 (unitSheaf X) := by
  let P := presheafToSheaf (Scheme.AffineEtale.topology X) C
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  have h : KummerUnitsPresheaf.power X d = d • 𝟙 (KummerUnitsPresheaf.units X) := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro a
    rfl
  change P.map (KummerUnitsPresheaf.power X d) = d • 𝟙 (P.obj (KummerUnitsPresheaf.units X))
  rw [h, Functor.map_nsmul, P.map_id]

private theorem p_comp (d m : ℕ) : p X m ≫ p X d = p X (d * m) := by
  rw [p_eq X m, p_eq X d, p_eq X (d * m), Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, smul_smul, Nat.mul_comm m d]

private def affineStep (d m : ℕ) :
    kernel (p X (d * m)) ⟶ kernel (p X d) :=
  kernel.lift (p X d) (kernel.ι (p X (d * m)) ≫ p X m) (by
    rw [Category.assoc, p_comp, kernel.condition])

/-- The true transition raising the actual degree-\(dm\) roots to the
\(m\)-th power on the full small étale site. -/
def rootsStep (d m : ℕ) : (S X (d * m)).X₁ ⟶ (S X d).X₁ :=
  (Q X).map (affineStep X d m)

theorem rootsStep_inclusion (d m : ℕ) :
    rootsStep X d m ≫ (S X d).f = (S X (d * m)).f ≫ (S X m).g := by
  change (Q X).map (affineStep X d m) ≫ (Q X).map (kernel.ι (p X d)) =
    (Q X).map (kernel.ι (p X (d * m))) ≫ (Q X).map (p X m)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => (Q X).map f) (kernel.lift_ι _ _ _)

theorem cohomologyPower (d n : ℕ) (x : Sheaf.H (U X) n) :
    Sheaf.H.map (S X d).g n x = d • x := by
  let F := Sheaf.functorH X.smallEtaleTopology n
  change (F.map (S X d).g).hom x = _
  rw [KummerRelativeFull.power_nsmul, Functor.map_nsmul, F.map_id] <;> rfl

private abbrev ints := (constantSheaf X.smallEtaleTopology C).obj (AddCommGrpCat.of (ULift.{0} ℤ))

variable {X}
variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))
variable (d : ℕ) (hpos : 0 < d) [hdK : NeZero (d : K)]
variable (hu : Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ d))

include hu in
private theorem degreeZero_power_surjective : Function.Surjective (Sheaf.H.map (S X d).g 0) := by
  let e := (((Sheaf.functorH X.smallEtaleTopology 0).mapIso
    (KummerRelativeFull.unitsIso (X := X) d)).addCommGroupIsoToAddEquiv).symm.trans
    (degreeZeroUnitEquiv X)
  intro u
  obtain ⟨a, ha⟩ := hu (e u).toMul
  refine ⟨e.symm (Additive.ofMul a), e.injective ?_⟩
  rw [cohomologyPower, map_nsmul, e.apply_symm_apply]
  change Additive.ofMul (a ^ d) = e u
  exact congrArg Additive.ofMul (show a ^ d = (e u).toMul from ha)

include k hpos hdK in
private theorem inclusion_exact :
    Function.Exact (Sheaf.H.map (S X d).f 1) (Sheaf.H.map (S X d).g 1) := by
  have h := Ext.covariant_sequence_exact₂' (ints X)
    (KummerRelativeFull.sequence_shortExact k d hpos) 1
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

include k hpos hdK hu in
private theorem inclusion_injective :
    Function.Injective (Sheaf.H.map (S X d).f 1) := by
  let hS := KummerRelativeFull.sequence_shortExact k d hpos
  let δ := hS.extClass.postcomp (ints X) (show 0 + 1 = 1 by rfl)
  have hδ : Function.Exact (Sheaf.H.map (S X d).g 0) δ := by
    have h := Ext.covariant_sequence_exact₃' (ints X) hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hι : Function.Exact δ (Sheaf.H.map (S X d).f 1) := by
    have h := Ext.covariant_sequence_exact₁' (ints X) hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  intro x y hxy
  have hzero : Sheaf.H.map (S X d).f 1 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (hι (x - y)).1 hzero
  exact sub_eq_zero.mp (hz.symm.trans ((hδ z).2 (degreeZero_power_surjective d hu z)))

include k hpos hdK hu in
/-- Finite cohomology of the actual full root kernel gives precisely
the torsion subgroup inside the true unit cohomology group. -/
def kernelHOneEquiv : Sheaf.H (S X d).X₁ 1 ≃+ killedBy (Sheaf.H (U X) 1) d := by
  let i := Sheaf.H.map (S X d).f 1
  let h := inclusion_exact k d hpos
  let f : Sheaf.H (S X d).X₁ 1 →+ killedBy (Sheaf.H (U X) 1) d :=
    { toFun := fun x => ⟨i x, by
        change d • i x = 0
        rw [← cohomologyPower X d 1]
        exact (h (i x)).2 ⟨x, rfl⟩⟩
      map_zero' := Subtype.ext i.map_zero
      map_add' := fun a b => Subtype.ext (i.map_add a b) }
  refine AddEquiv.ofBijective f ⟨fun x y hxy => inclusion_injective k d hpos hu
    (congrArg Subtype.val hxy), ?_⟩
  intro z
  have hz : Sheaf.H.map (S X d).g 1 z.val = 0 :=
    (cohomologyPower X d 1 z.val).trans z.property
  obtain ⟨x, hx⟩ := (h z.val).1 hz
  exact ⟨x, Subtype.ext hx⟩

theorem kernelHOneEquiv_value (x : Sheaf.H (S X d).X₁ 1) :
    (kernelHOneEquiv k d hpos hu x).val = Sheaf.H.map (S X d).f 1 x := rfl

variable (m : ℕ) (hm : 0 < d * m) [NeZero ((d * m : ℕ) : K)]
variable (hum : Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ (d * m)))

/-- On native finite-coefficient cohomology the literal root transition
induces multiplication by its exponent in unit cohomology torsion. -/
theorem kernelHOneEquiv_step (x : Sheaf.H (S X (d * m)).X₁ 1) :
    kernelHOneEquiv k d hpos hu (Sheaf.H.map (rootsStep X d m) 1 x) =
      killedByTransition (Sheaf.H (U X) 1) d m (kernelHOneEquiv k (d * m) hm hum x) := by
  apply Subtype.ext
  change Sheaf.H.map (S X d).f 1 (Sheaf.H.map (rootsStep X d m) 1 x) =
    m • Sheaf.H.map (S X (d * m)).f 1 x
  rw [← Sheaf.H.map_comp_apply, rootsStep_inclusion, Sheaf.H.map_comp_apply]
  exact cohomologyPower X m 1 (Sheaf.H.map (S X (d * m)).f 1 x)

end

end ManuscriptAudit.FullEtaleKummerKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FullEtaleKummerKernel.kernelHOneEquiv_value,
      ``ManuscriptAudit.FullEtaleKummerKernel.kernelHOneEquiv_step] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
