import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologyDegreeTwo
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull

/-! Native finite Kummer first cohomology on the full small étale site. -/

namespace ManuscriptAudit.FullEtaleKummerHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open KummerUnitsSheaf KummerRelativeFull KummerCohomologyDegreeTwo

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev J (X : Scheme.{0}) := X.smallEtaleTopology
private abbrev A := AddCommGrpCat.{0}
private abbrev integerConstant (X : Scheme.{0}) :=
  (constantSheaf (J X) A).obj (AddCommGrpCat.of (ULift.{0} ℤ))

/-- Actual degree-zero unit cohomology is the group of global scheme units. -/
def degreeZeroUnitEquiv (X : Scheme.{0}) :
    Sheaf.H (fullCoordinateUnitSheaf X) 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
  Sheaf.H.equiv₀ (fullCoordinateUnitSheaf X) (MorphismProperty.Over.mkIdTerminal @Etale X)

private theorem cohomologyPower (X : Scheme.{0}) (d n : ℕ)
    (x : Sheaf.H (sequence X d).X₂ n) :
    Sheaf.H.map (sequence X d).g n x = d • x := by
  let F := Sheaf.functorH (J X) n
  change (F.map (sequence X d).g).hom x = _
  rw [power_nsmul, Functor.map_nsmul]
  have hId : F.map (𝟙 (sequence X d).X₂) = 𝟙 (F.obj (sequence X d).X₂) :=
    F.map_id (sequence X d).X₂
  rw [hId] <;> rfl

private def killedByCongr {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) : killedBy G d ≃+ killedBy H d where
  toFun u := ⟨e u.val, by
    change d • e u.val = 0
    rw [← map_nsmul, show d • u.val = 0 from u.property, map_zero]⟩
  invFun v := ⟨e.symm v.val, by
    change d • e.symm v.val = 0
    rw [← map_nsmul, show d • v.val = 0 from v.property, map_zero]⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (e.map_add u.val v.val)

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

/-- If the power map is onto on actual global units, constant roots H¹ on
the full small étale site is actual unit-cohomology torsion. -/
def geometricRootsHOneEquiv (d : ℕ) [NeZero (d : K)]
    (hUnits : Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ d)) :
    Sheaf.H ((constantSheaf (J X) A).obj (KummerConstantCoefficients.coefficientGroup K d)) 1 ≃+
      killedBy (Sheaf.H (fullCoordinateUnitSheaf X) 1) d := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let S := sequence X d
  let hS := sequence_shortExact k d hpos
  let e₀ : Sheaf.H S.X₂ 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
    (((Sheaf.functorH (J X) 0).mapIso (unitsIso X d)).addCommGroupIsoToAddEquiv).symm.trans
      (degreeZeroUnitEquiv X)
  have hSurj : Function.Surjective (Sheaf.H.map S.g 0) := by
    intro u
    obtain ⟨a, ha⟩ := hUnits (e₀ u).toMul
    refine ⟨e₀.symm (Additive.ofMul a), e₀.injective ?_⟩
    rw [cohomologyPower X d 0, map_nsmul, e₀.apply_symm_apply]
    change Additive.ofMul (a ^ d) = e₀ u
    rw [ha, ofMul_toMul]
  let i : Sheaf.H S.X₁ 1 →+ Sheaf.H S.X₂ 1 := Sheaf.H.map S.f 1
  let g : Sheaf.H S.X₂ 1 →+ Sheaf.H S.X₂ 1 := Sheaf.H.map S.g 1
  let δ := hS.extClass.postcomp (integerConstant X) (show 0 + 1 = 1 by rfl)
  have hδ : Function.Exact (Sheaf.H.map S.g 0) δ := by
    have h := Ext.covariant_sequence_exact₃' (integerConstant X) hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hι : Function.Exact δ i := by
    have h := Ext.covariant_sequence_exact₁' (integerConstant X) hS 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  have hExact : Function.Exact i g := by
    have h := Ext.covariant_sequence_exact₂' (integerConstant X) hS 1
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact h
  let mapTorsion : Sheaf.H S.X₁ 1 →+ killedBy (Sheaf.H S.X₂ 1) d :=
    { toFun := fun x => ⟨i x, by
        change d • i x = 0
        rw [← cohomologyPower X d 1]
        exact (hExact (i x)).2 ⟨x, rfl⟩⟩
      map_zero' := Subtype.ext i.map_zero
      map_add' := fun x y => Subtype.ext (i.map_add x y) }
  have hBij : Function.Bijective mapTorsion := by
    constructor
    · intro x y hxy
      have hEq : i x = i y := congrArg
        (fun a : killedBy (Sheaf.H S.X₂ 1) d => a.val) hxy
      have hZero : i (x - y) = 0 := by rw [map_sub, hEq, sub_self]
      obtain ⟨z, hz⟩ := (hι (x - y)).1 hZero
      have hδZero : δ z = 0 := (hδ z).2 (hSurj z)
      exact sub_eq_zero.mp (hz.symm.trans hδZero)
    · intro y
      have hy : g y.val = 0 := (cohomologyPower X d 1 y.val).trans y.property
      obtain ⟨x, hx⟩ := (hExact y.val).1 hy
      exact ⟨x, Subtype.ext hx⟩
  let e₁ := ((Sheaf.functorH (J X) 1).mapIso (firstIso (d := d) k)).addCommGroupIsoToAddEquiv
  let e₂ := ((Sheaf.functorH (J X) 1).mapIso (unitsIso X d)).addCommGroupIsoToAddEquiv
  exact e₁.trans ((AddEquiv.ofBijective mapTorsion hBij).trans (killedByCongr e₂.symm d))

end

end ManuscriptAudit.FullEtaleKummerHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FullEtaleKummerHOne.degreeZeroUnitEquiv,
      ``ManuscriptAudit.FullEtaleKummerHOne.geometricRootsHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
