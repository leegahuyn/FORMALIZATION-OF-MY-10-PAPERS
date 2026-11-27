import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleUnitComparison
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSequence

/-! The actual change-of-site map intertwines the two Kummer sequences and their boundaries. -/

namespace ManuscriptAudit.EtaleProetaleKummerComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.Preadditive
open EtaleProetaleInverseImage EtaleProetaleUnitComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev E := Sheaf X.smallEtaleTopology AddCommGrpCat.{1}
private abbrev D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}

local instance etaleHasExt : HasExt.{1} (E X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology AddCommGrpCat.{1}
  exact IsGrothendieckAbelian.hasExt _

local instance inverseImageAdditive : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private abbrev coefficientLift :=
  sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{1}

def etaleSequence (d : ℕ) : ShortComplex (E X) :=
  (KummerRelativeFull.sequence X d).map (coefficientLift X)

private def etaleSequenceUnits (d : ℕ) : etaleUnits X ≅ (etaleSequence X d).X₂ :=
  (coefficientLift X).mapIso (KummerRelativeFull.unitsIso (X := X) d)

private theorem etale_sequence_power (d : ℕ) :
    (etaleSequence X d).g = d • 𝟙 (etaleSequence X d).X₂ := by
  let F := coefficientLift X
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  change F.map (KummerRelativeFull.sequence X d).g = _
  rw [KummerRelativeFull.power_nsmul, Functor.map_nsmul, F.map_id]

private def unitSquare (d : ℕ) :
    (inverseImage X).obj (etaleSequence X d).X₂ ⟶ proetaleUnits X :=
  (inverseImage X).map (etaleSequenceUnits X d).inv ≫ unitComparison X

private theorem unit_square_commutes (d : ℕ) :
    (inverseImage X).map (etaleSequence X d).g ≫ unitSquare X d =
      unitSquare X d ≫ ProetaleKummerPower.power X d := by
  rw [etale_sequence_power, Functor.map_nsmul, (inverseImage X).map_id,
    ProetaleKummerPower.power, nsmul_comp, id_comp, comp_nsmul, comp_id]

/-- The native morphism to the actual pro-étale Kummer sequence. -/
def sequenceComparison (d : ℕ) :
    (etaleSequence X d).map (inverseImage X) ⟶ ProetaleKummerSequence.sequence X d where
  τ₁ := kernel.lift (ProetaleKummerPower.power X d)
    ((inverseImage X).map (etaleSequence X d).f ≫ unitSquare X d) (by
      rw [Category.assoc, ← unit_square_commutes, ← Category.assoc, ← Functor.map_comp,
        (etaleSequence X d).zero, Functor.map_zero, zero_comp])
  τ₂ := unitSquare X d
  τ₃ := unitSquare X d
  comm₁₂ := by
    change kernel.lift _ _ _ ≫ kernel.ι _ = _
    exact kernel.lift_ι _ _ _
  comm₂₃ := (unit_square_commutes X d).symm


theorem boundary_comparison (d n : ℕ)
    (hEtale : (etaleSequence X d).ShortExact)
    (hProetale : (ProetaleKummerSequence.sequence X d).ShortExact)
    (e : Sheaf.H (etaleSequence X d).X₃ n) :
    Sheaf.H.map (sequenceComparison X d).τ₁ (n+1)
      (EtaleProetaleCohomologyMap.pullback X (etaleSequence X d).X₁ (n+1)
        (e.comp hEtale.extClass rfl)) =
      (Sheaf.H.map (sequenceComparison X d).τ₃ n
        (EtaleProetaleCohomologyMap.pullback X (etaleSequence X d).X₃ n e)).comp
          hProetale.extClass rfl := by
  rw [EtaleProetaleCohomologyMap.pullback_boundary X hEtale n e]
  let e' := EtaleProetaleCohomologyMap.pullback X (etaleSequence X d).X₃ n e
  let h := hEtale.map_of_exact (inverseImage X)
  let f := sequenceComparison X d
  change (e'.comp h.extClass rfl).comp (Ext.mk₀ f.τ₁) (add_zero (n+1)) =
    (e'.comp (Ext.mk₀ f.τ₃) (add_zero n)).comp hProetale.extClass rfl
  have hNat := h.extClass_naturality hProetale f
  rw [Ext.comp_assoc_of_third_deg_zero, hNat, ← Ext.comp_assoc_of_second_deg_zero]

end
end ManuscriptAudit.EtaleProetaleKummerComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleKummerComparison.sequenceComparison,
      ``ManuscriptAudit.EtaleProetaleKummerComparison.boundary_comparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
