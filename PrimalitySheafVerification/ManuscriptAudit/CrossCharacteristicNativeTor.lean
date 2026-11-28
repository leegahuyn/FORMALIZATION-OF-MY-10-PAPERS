import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.CrossCharacteristicDerivedCone

/-! Every actual integral Tor group of two abelian groups with coprime
scalar annihilators vanishes. The argument applies to Mathlib's
left-derived tensor in all degrees, including degree zero. -/

namespace ManuscriptAudit.CrossCharacteristicNativeTor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := ModuleCat.{0} ℤ
private abbrev c := ComplexShape.down ℕ

private theorem morphism_smul_zero (X : C) (p : ℕ)
    (hp : ∀ x : X, (p : ℤ) • x = 0) : (p : ℤ) • 𝟙 X = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact hp x

private theorem isZero_of_id (X : C) (h : 𝟙 X = 0) : IsZero X := by
  let i : X ≅ 0 :=
    { hom := 0
      inv := 0
      hom_inv_id := by simpa only [comp_zero] using h.symm
      inv_hom_id := (isZero_zero C).eq_of_src _ _ }
  exact i.isZero_iff.mpr (isZero_zero C)

private theorem homology_smul_zero (M N : C) {p : ℕ}
    (hp : (p : ℤ) • 𝟙 M = 0) (n : ℕ) :
    (p : ℤ) • 𝟙 (((Tor C n).obj M).obj N) = 0 := by
  let P := projectiveResolution N
  let F := (tensoringLeft C).obj M
  let K := (F.mapHomologicalComplex c).obj P.complex
  have hK : (p : ℤ) • 𝟙 K = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    let E := HomologicalComplex.eval C c i
    let G := (tensoringRight C).obj (P.complex.X i)
    change E.map ((p : ℤ) • 𝟙 K) = E.map 0
    rw [E.map_zsmul, E.map_id, E.map_zero]
    change (p : ℤ) • 𝟙 (G.obj M) = 0
    simpa only [G.map_zsmul, G.map_id, G.map_zero] using congrArg G.map hp
  let H := HomologicalComplex.homologyFunctor C c n
  have hH : (p : ℤ) • 𝟙 (H.obj K) = 0 := by
    simpa only [H.map_zsmul, H.map_id, H.map_zero] using congrArg H.map hK
  let e := P.isoLeftDerivedObj F n
  have he := congrArg (fun a : H.obj K ⟶ H.obj K ↦ e.hom ≫ a ≫ e.inv) hH
  have hs : e.hom ≫ ((p : ℤ) • 𝟙 (H.obj K)) ≫ e.inv =
      (p : ℤ) • 𝟙 (((Tor C n).obj M).obj N) := by
    rw [← Category.assoc, Preadditive.comp_zsmul, Category.comp_id,
      Preadditive.zsmul_comp, e.hom_inv_id]
  exact hs.symm.trans (he.trans (by rw [zero_comp, comp_zero]))

private theorem derived_map_scalar_id (F : C ⥤ C) [F.Additive] (N : C)
    (n : ℕ) (a : ℤ) : (F.leftDerived n).map (a • 𝟙 N) =
      a • 𝟙 ((F.leftDerived n).obj N) := by
  let P := projectiveResolution N
  let S := ChainComplex.single₀ C
  have w : (a • 𝟙 P.complex) ≫ P.π = P.π ≫ S.map (a • 𝟙 N) := by
    rw [S.map_zsmul, S.map_id, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Category.id_comp, Category.comp_id]
  let L := F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor C c n
  let e := P.isoLeftDerivedObj F n
  calc
    _ = e.hom ≫ L.map (a • 𝟙 P.complex) ≫ e.inv :=
      F.leftDerived_map_eq n (a • 𝟙 N) (a • 𝟙 P.complex) w
    _ = _ := by
      rw [L.map_zsmul, L.map_id, ← Category.assoc, Preadditive.comp_zsmul,
        Category.comp_id, Preadditive.zsmul_comp, e.hom_inv_id]

/-- This is the genuine Tor object for every choice of derived degree. -/
theorem isZero_Tor_of_coprime (M N : C) {p l : ℕ} (hc : p.Coprime l)
    (hp : ∀ x : M, (p : ℤ) • x = 0) (hl : ∀ x : N, (l : ℤ) • x = 0) (n : ℕ) :
    IsZero (((Tor C n).obj M).obj N) := by
  let F := (tensoringLeft C).obj M
  let T := F.leftDerived n
  have h₀ : T.map (0 : N ⟶ N) = 0 := by
    simpa only [zero_smul] using derived_map_scalar_id F N n (0 : ℤ)
  have hL : (l : ℤ) • 𝟙 (T.obj N) = 0 :=
    (derived_map_scalar_id F N n l).symm.trans
      ((congrArg T.map (morphism_smul_zero N l hl)).trans h₀)
  let e := CrossCharacteristicDerivedCone.scalarIso hc
    (homology_smul_zero M N (morphism_smul_zero M p hp) n)
  apply isZero_of_id
  have he : e.hom ≫ e.inv = 0 := by
    change ((l : ℤ) • 𝟙 (T.obj N)) ≫ e.inv = 0
    rw [hL, zero_comp]
  exact e.hom_inv_id.symm.trans he

/-- The genuine derived Tor groups against coprime cyclic coefficients vanish. -/
theorem isZero_Tor_zmod_of_coprime {M : Type} [AddCommGroup M] {p l : ℕ}
    [Module (ZMod p) M] (hc : p.Coprime l) (n : ℕ) :
    IsZero (((Tor C n).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ (ZMod l))) := by
  apply isZero_Tor_of_coprime _ _ hc _ _ n
  · intro x
    change (p : ℤ) • (x : M) = 0
    rw [← Int.cast_smul_eq_zsmul (ZMod p) (p : ℤ) x, Int.cast_natCast,
      ZMod.natCast_self, zero_smul]
  · intro x
    change (l : ℤ) • (x : ZMod l) = 0
    rw [← Int.cast_smul_eq_zsmul (ZMod l) (l : ℤ) x, Int.cast_natCast,
      ZMod.natCast_self, zero_smul]

end
end ManuscriptAudit.CrossCharacteristicNativeTor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CrossCharacteristicNativeTor.isZero_Tor_of_coprime,
      ``ManuscriptAudit.CrossCharacteristicNativeTor.isZero_Tor_zmod_of_coprime] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
