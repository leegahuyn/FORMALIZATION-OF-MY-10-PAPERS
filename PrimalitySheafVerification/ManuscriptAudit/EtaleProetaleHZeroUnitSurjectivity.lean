import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCohomologyMap

/-! Surjectivity of the actual unit on terminal sections implies
surjectivity of the literal degree-zero inverse-image map. -/

namespace ManuscriptAudit.EtaleProetaleHZeroUnitSurjectivity

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleProetaleInverseImage (inverseImage directImage adjunction constantInverseImageIso)
open EtaleProetaleCohomologyMap (pullback)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{1}
private abbrev C := Sheaf X.smallEtaleTopology A
private abbrev E := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev ZE := (constantSheaf X.smallEtaleTopology A).obj E
private abbrev ZP := (constantSheaf (Scheme.ProEt.topology X) A).obj E
private abbrev T := Scheme.Etale.mk (𝟙 X)
private abbrev j := (constantInverseImageIso X).app E

local instance : HasExt.{1} (C X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology A
  exact IsGrothendieckAbelian.hasExt _

local instance : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private def integralMultiples {G : A} (y : G) : E ⟶ G :=
  AddCommGrpCat.ofHom
    { toFun := fun n ↦ n.down • y
      map_zero' := zero_zsmul y
      map_add' := fun m n ↦ add_zsmul y m.down n.down }

private theorem integralMultiples_unique {G : A} (p q : E ⟶ G)
    (h : p (ULift.up 1) = q (ULift.up 1)) : p = q := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  have hz : z.down • (ULift.up 1 : ULift.{1} ℤ) = z := by
    rcases z with ⟨n⟩
    change ULift.up (n • (1 : ℤ)) = ULift.up n
    rw [zsmul_eq_mul, mul_one]
  change p z = q z
  rw [← hz]
  exact (p.hom.map_zsmul _ _).trans ((congrArg (fun v : G ↦ z.down • v) h).trans (q.hom.map_zsmul _ _).symm)

set_option maxHeartbeats 3600000 in
/-- The actual degree-zero cohomology comparison is surjective if its
own adjunction unit induces a surjection on global sections. -/
theorem pullback_zero_surjective (F : C X)
    (hUnit : Function.Surjective (((adjunction X).unit.app F).hom.app (op (T X)))) :
    Function.Surjective (pullback X F 0) := by
  intro x
  let L := inverseImage X
  let R := directImage X
  let a := adjunction X
  let η := a.unit.app F
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (ZP X) (L.obj F)).surjective x
  let h := a.homEquiv (ZE X) (L.obj F) ((j X).hom ≫ g)
  let a₀ := constantSheafAdj X.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  let v := a₀.homEquiv E (R.obj (L.obj F)) h
  obtain ⟨y, hy⟩ := hUnit (v (ULift.up 1))
  let p := integralMultiples y
  let f := (a₀.homEquiv E F).symm p
  have hη : f ≫ η = h := by
    apply (a₀.homEquiv E (R.obj (L.obj F))).injective
    rw [Adjunction.homEquiv_naturality_right]
    change (a₀.homEquiv E F ((a₀.homEquiv E F).symm p)) ≫ η.hom.app (op (T X)) = v
    rw [Equiv.apply_symm_apply]
    apply integralMultiples_unique
    change η.hom.app (op (T X)) ((1 : ℤ) • y) = v (ULift.up 1)
    simpa only [one_zsmul] using hy
  have hf : L.map f = (j X).hom ≫ g := by
    apply (a.homEquiv (ZE X) (L.obj F)).injective
    have hm := a.homEquiv_naturality_left f (𝟙 (L.obj F))
    rw [Category.comp_id, Adjunction.homEquiv_id] at hm
    exact hm.trans hη
  refine ⟨Ext.mk₀ f, ?_⟩
  change (Ext.mk₀ (j X).inv).comp ((Ext.mk₀ f).mapExactFunctor L) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, hf, Iso.inv_hom_id_assoc]

end
end ManuscriptAudit.EtaleProetaleHZeroUnitSurjectivity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleHZeroUnitSurjectivity.pullback_zero_surjective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
