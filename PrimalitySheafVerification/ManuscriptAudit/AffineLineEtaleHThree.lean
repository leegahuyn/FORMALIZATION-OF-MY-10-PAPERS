import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorDegreeTwo
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.RatFuncGenericImageHigher

/-! Native affine-line étale H³ vanishing for units and invertible cyclic coefficients. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open GeometricSkyscraperCohomology KummerUnitsSheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private theorem H_succ_subsingleton_of_quotient_and_middle {Y : Scheme.{0}}
    (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{0})) (hS : S.ShortExact)
    (n : ℕ) (hQ : Subsingleton (Sheaf.H S.X₃ n))
    (hM : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  let Z := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))
  apply subsingleton_of_forall_eq 0
  intro x
  change Ext Z S.X₁ (n + 1) at x
  have hx : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := hM.elim _ _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (show n + 1 = n + 1 by rfl)
  have hyZero : y = 0 := hQ.elim _ _
  change x = 0
  rw [← hy, hyZero, Ext.zero_comp]

variable (K : Type) [Field K] [IsAlgClosed K]

/-- The regular full-small-étale unit sheaf of the affine line has zero H². -/
theorem affineLine_units_HTwo_subsingleton :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (X K)) 2) :=
  H_succ_subsingleton_of_quotient_and_middle (divisorSequence K (RatFunc K))
    (divisorSequence_shortExact K (RatFunc K)) 1 (divisor_HOne_subsingleton K)
    (RatFuncTsen.affineLine_genericUnitImage_H_succ_subsingleton K 1)

/-- The actual regular unit sheaf of the affine line has zero H³. -/
theorem affineLine_units_HThree_subsingleton :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (X K)) 3) :=
  H_succ_subsingleton_of_quotient_and_middle (divisorSequence K (RatFunc K))
    (divisorSequence_shortExact K (RatFunc K)) 2 (divisor_HTwo_subsingleton K)
    (RatFuncTsen.affineLine_genericUnitImage_H_succ_subsingleton K 2)

/-- The full small-étale constant cyclic sheaf of order invertible in K
has zero H³ on the affine line. -/
theorem affineLine_cyclic_HThree_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 3) := by
  let k : X K ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))
  letI : NeZero d := NeZero.of_neZero_natCast K
  let S := KummerRelativeFull.sequence (X K) d
  have hS : S.ShortExact := KummerRelativeFull.sequence_shortExact k d (Nat.pos_of_ne_zero (NeZero.ne d))
  let e := KummerRelativeFull.unitsIso (X := X K) d
  let H (n : ℕ) := (((Sheaf.functorH (X K).smallEtaleTopology n).mapIso e).addCommGroupIsoToAddEquiv)
  have h₃ : Subsingleton (Sheaf.H S.X₃ 2) := by
    let h := affineLine_units_HTwo_subsingleton K
    exact ⟨fun a b ↦ (H 2).symm.injective (h.elim _ _)⟩
  have h₂ : Subsingleton (Sheaf.H S.X₂ 3) := by
    let h := affineLine_units_HThree_subsingleton K
    exact ⟨fun a b ↦ (H 3).symm.injective (h.elim _ _)⟩
  have h₁ := H_succ_subsingleton_of_quotient_and_middle S hS 2 h₃ h₂
  let eRoots : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let eCoefficients := (constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).mapIso
    (eRoots.toAddCommGrpIso :
      KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let eFirst := eCoefficients.symm ≪≫ KummerRelativeFull.firstIso (d := d) k
  let eH := ((Sheaf.functorH (X K).smallEtaleTopology 3).mapIso eFirst).addCommGroupIsoToAddEquiv
  exact ⟨fun a b ↦ eH.injective (h₁.elim _ _)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineLine_units_HThree_subsingleton,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineLine_cyclic_HThree_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
