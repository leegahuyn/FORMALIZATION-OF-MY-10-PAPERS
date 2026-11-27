import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafPositiveResolutionCohomology

/-! Naturality of positive finite-level sheaf cohomology computed by evaluated injective resolutions. -/

namespace ManuscriptAudit.SheafPositiveResolutionNaturality

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open SheafTerminalSectionsAsHoms (sections homEquiv homEquiv_symm_map)
open SheafPositiveResolutionCohomology (sectionsShort cycleClass cycleClass_kernel
  cycleClass_surjective positiveEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}

variable [HasSheafify J A] [HasExt.{0} (Sheaf J A)]

local instance sections_additive (T : C) : (sections J T).Additive :=
  ⟨by intros; rfl⟩

variable {T : C} (hT : IsTerminal T)
variable {F G : Sheaf J A} {R : InjectiveResolution F} {P : InjectiveResolution G}
variable {f : F ⟶ G} (φ : InjectiveResolution.Hom R P f)

/-- The native short-complex map of evaluated terms of a resolution lift. -/
def shortMap (n : ℕ) : sectionsShort J R n (T := T) ⟶ sectionsShort J P n (T := T) where
  τ₁ := (sections J T).map (φ.hom.f n)
  τ₂ := (sections J T).map (φ.hom.f (n + 1))
  τ₃ := (sections J T).map (φ.hom.f (n + 2))
  comm₁₂ := by
    change (sections J T).map (φ.hom.f n) ≫ (sections J T).map (P.cocomplex.d n (n + 1)) =
      (sections J T).map (R.cocomplex.d n (n + 1)) ≫ (sections J T).map (φ.hom.f (n + 1))
    simpa only [Functor.map_comp] using congrArg ((sections J T).map) (φ.hom.comm n (n + 1))
  comm₂₃ := by
    change (sections J T).map (φ.hom.f (n + 1)) ≫ (sections J T).map (P.cocomplex.d (n + 1) (n + 2)) =
      (sections J T).map (R.cocomplex.d (n + 1) (n + 2)) ≫ (sections J T).map (φ.hom.f (n + 2))
    simpa only [Functor.map_comp] using congrArg ((sections J T).map) (φ.hom.comm (n + 1) (n + 2))

private theorem cycle_value (S : ShortComplex A) (x : S.cycles) :
    (S.abCyclesIso.hom x).val = S.iCycles x := by
  have h := S.abCyclesIso_inv_apply_iCycles (S.abCyclesIso.hom x)
  change S.iCycles ((S.abCyclesIso.hom ≫ S.abCyclesIso.inv) x) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

private theorem positiveEquiv_on_cycle (I : InjectiveResolution F) (n : ℕ)
    (x : (sectionsShort J I n (T := T)).cycles) :
    positiveEquiv J hT I n ((sectionsShort J I n (T := T)).homologyπ x) =
      cycleClass J hT I n ((sectionsShort J I n (T := T)).abCyclesIso.hom x) := by
  let S := sectionsShort J I n (T := T)
  have h := CategoryTheory.congr_fun S.abLeftHomologyData.homologyπ_comp_homologyIso_hom x
  change S.abHomologyIso.hom (S.homologyπ x) =
    QuotientAddGroup.mk (S.abCyclesIso.hom x) at h
  change ((QuotientAddGroup.quotientAddEquivOfEq (cycleClass_kernel J hT I n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (cycleClass_surjective J hT I n)))
      (S.abHomologyIso.hom (S.homologyπ x)) = _
  rw [h] <;> rfl

private theorem cycle_naturality (n : ℕ)
    (x : (sectionsShort J R n (T := T)).cycles) :
    cycleClass J hT P n ((sectionsShort J P n (T := T)).abCyclesIso.hom
      (ShortComplex.cyclesMap (shortMap J φ n (T := T)) x)) =
      Sheaf.H.map f (n + 1) (cycleClass J hT R n ((sectionsShort J R n (T := T)).abCyclesIso.hom x)) := by
  let S := sectionsShort J R n (T := T)
  let D := sectionsShort J P n (T := T)
  let m := shortMap J φ n (T := T)
  let x₀ := S.abCyclesIso.hom x
  let y₀ := D.abCyclesIso.hom (ShortComplex.cyclesMap m x)
  have hxy : y₀.val = (sections J T).map (φ.hom.f (n + 1)) x₀.val := by
    change (D.abCyclesIso.hom (ShortComplex.cyclesMap m x)).val =
      m.τ₂ (S.abCyclesIso.hom x).val
    rw [cycle_value, cycle_value]
    exact CategoryTheory.congr_fun (ShortComplex.cyclesMap_i m) x
  let z := (homEquiv J hT (R.cocomplex.X (n + 1))).symm x₀.val
  have hz : z ≫ R.cocomplex.d (n + 1) (n + 2) = 0 := by
    change (homEquiv J hT _).symm x₀.val ≫ _ = _
    rw [← homEquiv_symm_map J hT]
    have hx : (sections J T).map (R.cocomplex.d (n + 1) (n + 2)) x₀.val = 0 := x₀.property
    rw [hx, map_zero]
  change P.extMk ((homEquiv J hT (P.cocomplex.X (n + 1))).symm y₀.val) (n + 2) rfl _ =
    (R.extMk z (n + 2) rfl hz).comp (Ext.mk₀ f) (add_zero _)
  have hcomp : (homEquiv J hT (P.cocomplex.X (n + 1))).symm y₀.val =
      z ≫ φ.hom.f (n + 1) := by rw [hxy, homEquiv_symm_map] <;> rfl
  refine Eq.trans ?_ (R.extMk_comp_mk₀ z (n + 2) rfl hz φ).symm
  congr 1 <;> exact hcomp

/-- The evaluated resolution comparison gives exactly the native map on positive sheaf Ext. -/
theorem positiveEquiv_natural (n : ℕ) (x : (sectionsShort J R n (T := T)).homology) :
    positiveEquiv J hT P n (ShortComplex.homologyMap (shortMap J φ n (T := T)) x) =
      Sheaf.H.map f (n + 1) (positiveEquiv J hT R n x) := by
  let S := sectionsShort J R n (T := T)
  let m := shortMap J φ n (T := T)
  obtain ⟨v, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  change positiveEquiv J hT P n (ShortComplex.homologyMap m (S.homologyπ v)) = _
  have h := CategoryTheory.congr_fun (ShortComplex.homologyπ_naturality m) v
  simp only [h, positiveEquiv_on_cycle]
  exact cycle_naturality J hT φ n v

end
end ManuscriptAudit.SheafPositiveResolutionNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafPositiveResolutionNaturality.positiveEquiv_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
