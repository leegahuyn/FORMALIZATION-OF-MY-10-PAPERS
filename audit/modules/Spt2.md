# Spt2 감사 보고서 (`PrimalitySheafVerification/Spt2.lean`, 8,878줄)

감사 범위: 1–8878줄을 처음부터 끝까지 순차적으로 모두 읽음(커버리지 로그는 맨 끝에 있음). 보조 자료로 `scan/decls_cls.json`(Spt2 선언 877개)을 썼고, 고정된 Mathlib 트리에서 보조정리 이름 28개를 grep으로 확인함. `lake`/`lean`은 실행하지 않음.

선언 통계(decls_cls.json 기준): theorem 572, lemma 10, def 165, abbrev 32, structure 74, inductive 3, example 18, instance 3. 정리 582개 중 accessor-projection 65개(11%), trivial_tactic 92개이며 정리 길이의 중앙값은 7줄.

---

## 1. 목적과 논문 대응

- 대상 논문: Lee Ga Hyun, *"Master Equivalence on Arithmetic Curves"*(헤더 3–5, 72행). 이 파일은 다섯 개의 하위 계층을 하나로 합친 것이다(1–26행). 그 다섯은 ① 핵심 계층과 논문 인터페이스(`Spt2.lean`), ② `AdditionalFormalization`, ③ `BypassCertificate`, ④ `CompletionLayer`, ⑤ `GeometricWorkarounds`이고, 뒤에 wiring, audit, `StructuralResolution` 계층이 덧붙어 있다.
- 다루는 수학은 다음과 같다.
  - 산술 곡선 섬유 X_p에 대한 다섯 검출기(Alg/Geom, étale bump, motivic Euler jump, derived/T¹, Jacobian gate)의 동치. 이것이 Master Equivalence, Thm 1.1/6.1이다.
  - 판별식·Hensel 게이트(Thm 2.1, Prop 1.3/2.9/3.13).
  - CRT 접합(Lem 2.17, Prop 2.18, Lem 3.12).
  - 벤치마크 f = x^{pn}+y^A의 국소 길이 τ_p(§5.5).
  - 곡선의 정규화·dual graph·δ 공식(Lem 3.2, Thm 3.6, Prop 3.24/3.25).
  - 모티브 결함(Def 2.12, Prop 3.23/3.27).
  - 코탄젠트 복합체(Prop 5.1/5.3/5.5, Cor 5.4).
- 헤더의 §-map(80–98행)과 `PaperFullFormalization`(2430–2780행)이 논문의 거의 모든 번호 붙은 진술에 Lean 이름을 붙인다. 해당 진술은 Thm 1.1, 2.1, 2.4, 3.3, 3.6, 3.16, 3.28, 6.1, 6.9 / Prop 1.3, 1.6, 2.7, 2.9, 2.18, 3.10, 3.11, 3.13, 3.23–3.27, 3.30, 3.31, 5.1, 5.3, 5.5, 5.8, 6.10 / Cor 1.4, 1.5, 2.2, 2.6, 2.11, 2.15, 3.4, 3.7, 3.17, 5.4, 5.9, 6.4, 6.11 / Lem 2.17, 3.2, 3.12, 3.18, 6.6 / Rem 3.14 / Def 6.3 등이다.
- 파일 스스로 논문의 오류 세 가지를 공개적으로 정정한다. 이는 칭찬할 만하다.
  - (i) τ 표의 "p∣pn ∧ p∣A" 행은 pn·A가 아니라 ∞이다(100–104, 8181–8196행).
  - (ii) 논문이 H¹(L)과 T¹을 혼동하고 있다(2061–2156, 8206–8217행).
  - (iii) finrank는 무한차원을 0으로 붕괴시키므로 Module.length : ℕ∞를 써야 한다.

## 2. 헤드라인 정리 목록

상태 표기: (U) 무조건적 진짜 증명, (C) 이름 붙은 가정에 조건부, (A) accessor-projection, (T) 자명하거나 동어반복.

| # | 행 | Lean 이름 | 진술(요약) | 상태 |
|---|---|---|---|---|
| 1 | 697 | `Spt2.master_equivalence` | `(Hder : der = 0 ↔ smooth) (Hbump : bump = b1+deltaSum) (Hmot : mot = bump) (Hsing : smooth ↔ (b1=0 ∧ deltaSum=0)) : [smooth, bump=0, mot=0, der=0].TFAE` | C(순환) |
| 2 | 984 | `CurveModel.master_equivalence_curve` | `[f.IsSmooth, f.bump=0, f.mot=0, f.der=0].TFAE`. 독스트링은 "UNCONDITIONAL"이라고 함 | T |
| 3 | 2545/2751 | `PaperFullFormalization.theorem_1_1` / `theorem_6_1` | `[X.algSmooth, X.geomSmooth, X.etaleSilent, X.motivicSilent, X.derivedSilent].TFAE`, 구조체 필드 `alg_iff_*`의 사영 | A(순환) |
| 4 | 4119 | `BypassCertificate.CertifiedSPT2.master_equivalence` | 같은 5-TFAE를 "작은 인증서"들로부터 이행성으로 조립 | C(순환) |
| 5 | 8864 | `StructuralResolution.TautologyFreeCurve.master_equivalence` | #4를 `simpa`로 재포장한 것 | A |
| 6 | 566 | `squarefree_iff_coprime_derivative` | `Squarefree f ↔ IsCoprime f f'` (𝔽_p) | U(Mathlib 래퍼) |
| 7 | 1496 | `JacobianReal.localLength_eq_natDegree_gcd` | `finrank 𝔽_p (𝔽_p[X]/(f,f')) = natDegree (gcd f f')` | U |
| 8 | 1825 | `JacobianReal.formallyEtale_iff_squarefree_of_ne_zero` | `FormallyEtale 𝔽_p (AdjoinRoot f) ↔ Squarefree f` | U |
| 9 | 1882 | `JacobianReal.kaehlerEquivJacobianQuotient` | `Ω[A⁄𝔽_p] ≃ₗ[A] A ⧸ (f')` (A = 𝔽_p[X]/(f)) | U |
| 10 | 1717 | `JacobianReal.principalAQH1ModelEquivAlgebraH1Cotangent` | `ann_A(f') ≃ Algebra.H1Cotangent 𝔽_p A` (f≠0) | U |
| 11 | 2179 | `JacobianMv.formallySmooth_of_grad_span_eq_top` | 몫환 안에서 `(∂ᵢf) = ⊤`이면 `FormallySmooth 𝔽_p (MvPolynomial/(f))` (Jacobian 판정법의 한 방향, 82줄) | U |
| 12 | 3221 | `ActualAlgebra.int_dvd_resultant_derivative_iff_not_squarefree_mod` | 모닉 `F ∈ ℤ[X]`에 대해 `p ∣ Res(F,F') ↔ ¬Squarefree (F mod p)` | U |
| 13 | 4964 | `CompletionLayer.theorem_2_1_full_TFAE` | `¬Squarefree, ¬IsCoprime, Res=0, (대수폐체에서 임계점 존재), JacobianQuotient 비자명, localLength≠0`의 TFAE | U |
| 14 | 5163 | `CompletionLayer.Benchmark.benchSurface_jacobianQuotient_length_eq_top` | `p∣pn ∧ p∣A`이면 `Module.length 𝔽_p (𝔽_p[x,y]/(f,∂ₓf,∂ᵧf)) = ⊤` | U |
| 15 | 5714 | `HenselReal.every_residue_root_lifts_uniquely_of_squarefree_reduction` | `F mod p`가 squarefree이면 모든 잉여근이 ℤ_p로 유일하게 들어올려짐(`hensels_lemma` 이용) | U |
| 16 | 3626 | `EllipticCurveDiscriminant.goodReduction_iff_nonsingularReduction` | `¬ p ∣ -16(4a³+27b²) ↔ (W mod p).IsElliptic` | U(가벼움) |
| 17 | 6120 | `BenchmarkLocalLengthCompletion.originLocalTjurinaLength_finiteRows_eq_tau` | τ 표의 유한 3행, normal-form 인증서 3개에 조건부 | C(실질적이나 인스턴스 없음) |

## 3. 탈출구와 신뢰 기반

- 주석과 문자열을 제거한 사본에서 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`는 모두 0개다. lead의 확인과 일치한다.
- `set_option`은 하나뿐이다: 540행 `set_option synthInstance.maxHeartbeats 100000 in`(`quotientCotangentComplex_kernel_iff`).
- custom `elab`/`macro`/`syntax`는 없다. `instance`는 3개이고 모두 무해하다. 274행 `local instance ringHomInvPair_id_poly`, 1982행 `local instance : Fact (Nat.Prime 5)`, 5250행 `originIdeal_isPrime`이다.
- `decide`는 27회 쓰이는데 모두 작은 ℕ/ℕ∞ 계산이나 `List.length` 확인이다. 큰 항에 대한 `decide`는 없다.
- `Inhabited`, `default`, `Classical.choice`로 데이터를 날조하는 경우는 없다.
- **주장과 실제의 불일치**: 헤더 75–77행은 "`AxiomAudit` section runs `#print axioms` on each result"라고 하지만, `#print`는 파일에 단 한 번도 나오지 않는다. `section …AxiomAudit … end` 블록 19개(2783, 3660, 4805, 5377, 5502, 6870, 7202, 7699 … 8874행)는 전부 비어 있다. 공리 감사는 이 파일 안에서 실행되지 않는다.

## 4. 조건부 인증 감사 (핵심)

### (a) CIRCULAR: 가설이 결론을 그대로 말하거나 자명하게 함축함

1. **`master_equivalence` (697)**
   - `Hder : der = 0 ↔ smooth`가 그대로 TFAE의 1↔4 성분이다.
   - `Hmot : mot = bump`가 2↔3을, `Hbump`과 `Hsing`이 1↔2를 준다.
   - 결론 전체가 가설을 조립한 것일 뿐이다. `good_prime_box`(712)와 `curve_identity`(722)도 마찬가지다.
2. **`CurveModel.CurveFiber` (838)**
   - 필드 `mot_spec : mot = graph.b1 + Σδ`(849)와 `der_spec : der = graph.b1 + Σδ`(851)가 논문의 étale=motivic=derived 정리 그 자체다.
   - 여기에 정의 세 가지가 더해진다. `IsSmooth := b1 = 0 ∧ deltaSum = 0`(891), `H1Xp := 2g + b1 + Σδ`(876), `bump := H1Xp − H1Up`(883).
   - 따라서 `master_equivalence_curve`(984, 독스트링 "UNCONDITIONAL")와 `etale_motivic_equality`(931), `der_eq_zero_iff_smooth`(965)는 정의를 펼치고 `omega`를 적용한 것이다. 논문 Thm 1.1이 담은 내용은 전부 필드와 정의에 들어 있다.
3. **`PaperFullFormalization.ArithmeticCurve` (2451–2501)**
   - 탐지기 9개가 모두 임의의 `Prop`이다(`algSmooth … derivedSilent`, `baseChangeStable`, `crtGlue` …).
   - 필드 `alg_iff_geom`, `alg_iff_etaleSilent`, `alg_iff_motivicSilent`, `alg_iff_derivedSilent`(2475–2478)가 곧 Thm 1.1이다.
   - `hensel_iff_discriminant`는 Prop 1.3, `etale_motivic_equality`는 Thm 2.4/3.3/3.28/6.9/Prop 6.10, `h1_decomposition`은 Lem 3.2/Prop 3.24, `derived_dimension_formula`는 Prop 5.3, `base_change_identities : baseChangeStable`는 Thm 2.1/Prop 2.7/3.11/3.31/5.5다.
   - 2540–2778행의 논문 정리 약 45개는 모두 필드 사영이거나 그 결합이다.
   - 이 구조체에는 곡선(다항식, 스킴)이 아예 없다.
   - 추가로 `corollary_3_7`(2637)은 역방향 `hnoBump_to_good : X.bump = 0 → X.goodPrime`을 가설로 받는다. 결론의 절반을 가정하는 셈이다.
4. **`BypassCertificate.CertifiedSPT2` (4098)**
   - "monolithic bridge 필드를 쓰지 않는다"고 주장하지만, `algebraic_iff_geometric : algebraic.smooth ↔ geometricSmooth`(4101)는 옛 `alg_iff_geom` 필드와 글자 그대로 같다.
   - 나머지 다리도 필드들이다. `NormalizationCore.smooth_iff_no_defect`(3966), `EtaleCore.etaleSilent_iff_bump_zero`(3988), `MotiveCore.eulerJump_eq_bump`(4008, 곧 Thm 3.3 étale=motivic), `DerivedCore.derivedDimension_eq_localLength`(4038, 곧 Prop 5.3), `DerivedCore.localLength_zero_iff_smooth`(4040).
   - "derivation"은 이 필드들을 한두 단계 이행성으로 엮은 것에 불과하다.
   - `HenselCore.hensel_iff_discriminant`(3924)와 `BenchmarkCore.actualLength_eq_tauModel`(4080)도 결론 그 자체다.
5. **`TautologyFreeCurve` (8802)**: 이름과 독스트링("without tautological bridge fields")이 사실과 다르다. #4를 감싼 것이므로 순환성이 그대로 남아 있다.
6. **`ResultantDiscriminantComparison` (3280)**
   - 비모닉 경우의 핵심 주장인 `same_principalOpen_as_resultant : GoodPrimeByDelta Delta q ↔ GoodPrimeByDelta (Res F F') q`가 필드로 들어 있다.
   - `correctionFactor`와 `delta_eq_correction_mul_resultant` 필드는 어디에서도 쓰이지 않는다.
   - `correctedResultantDiscriminantCertificate`(3319)는 독스트링에서 "general-degree, non-monic case"라고 하면서 실제로는 `hF : F.Monic`을 요구한다.
7. **`MotiveRealizationCompatibilityCertificateT2.prop_3_27_realization_compatible` (6639)**: Prop 3.27을 글자 그대로 필드로 가정한다.

### (a′) 내용 없는 Prop+증명 쌍 (항상 `True`로 채울 수 있음)

해당 구조체: `SixFunctorBaseChangePackage`(1108), `NormalizationSheafCertificate`(5954), `EtaleFoundationCertificate`(6490), `EtaleLocalizationTriangleCertificate`(6552), `CertifiedMotiveTriangleT2.defectIsCone/localizationTriangle`(6578–6581), `DetectorSheafFloorCertificate`(7077), `DetectorSheafInstantiationCertificate`(8764), `DelegatedCitationNoHiddenDependencyChecklist`(7175), `ReplacementTargets.*`(3675–3839).

- 필드 이름이 "actual étale cohomology"를 말해도 타입은 임의의 `Prop`이다. 그래서 `floor_data`/`categorical_floor` 정리들은 accessor일 뿐이다.

### (b) SUBSTANTIVE: 그럴듯하게 참이고 결론과 분리된 깊은 입력

- `BenchmarkLocalLengthCompletion.OriginLocalJacobianNormalFormCertificate`(6049)는 국소 Tjurina 대수와 monomial box 사이의 선형 동형을 요구한다. 진짜 국소대수 입력이고 참이지만, 파일 어디에서도 인스턴스가 만들어지지 않는다.
- 비슷한 성격의 것으로 `MonomialBoxLengthCertificate`(6013), `LocalDeltaLengthCertificate`(6156)가 있다.
- `GradUnitCertificate`(2261)는 실질적이지만 #11의 가설과 사실상 같다.

### (c) SUSPECT-VACUOUS

- 모순되거나 만족 불가능한 가설은 발견되지 않았다.
- 오히려 반대 문제가 있다. `ArithmeticCurve`와 `CertifiedSPT2`는 모든 Prop을 `True`로, 모든 수를 0으로 두면 자명하게 만족된다. 그래서 "인증서가 inhabited다"라는 사실은 곡선에 대해 아무것도 말해주지 않는다.

### (d) DISCHARGED

- `DiscriminantCertificate F (Res F F')`: 모닉 F에 대해 `resultantDiscriminantCertificate`(3246)로 증명됨.
- `AlgebraicCore`: 실제 다항식 f로부터 `CompletionLayer.algebraicCoreOf`(5347)로 구성됨. 대수 부분의 앵커링은 진짜다.
- `NormalizationCore`, `EtaleCore`, `MotiveCore`는 wiring(6899, 6929, 6959)으로 "구성"된다. 그러나 이것은 해방(discharge)이 아니다.
  - `etaleSilent := dimH0Skyscraper = 0`이고, 그 수는 `Fin (b1+δ) → k`의 finrank, 즉 사용자가 넣은 숫자다.
  - `motiveCoreOfRealizationT2`는 인증서 인자 `_C`를 핵심 필드에 쓰지 않는다. `eulerJump_eq_bump`이 성립하는 이유는 `motivicEulerJumpT2 b1 δ := b1 + δ`(6176)라고 *정의*했기 때문이다.
  - `smooth_iff_no_defect`(곧 "매끄러움 ⇔ 특이점 없음")는 끝까지 가정으로 남는다.

### 참조 인스턴스 점검

- `ArithmeticCurve`, `CertifiedSPT2`, `TautologyFreeCurve`의 구체 인스턴스는 파일 전체에 단 하나도 없다. 실제 곡선이나 다항식에 묶인 인스턴스도 없다.
- `CurveModel.nodalExample`(1227)과 `smoothExample`(1249)은 장난감 숫자 인스턴스다. `mot := 9`, `der := 9`는 spec을 맞추도록 손으로 고른 값이다.
- 독스트링 "two nodes with δ = 3, 4"는 잘못된 표기다. 보통 node는 δ = 1이다(800행 `node` 정의도 δ=1).

## 5. 정의 충실도

**충실한 것 (Mathlib의 실제 개념을 씀)**
- Ideal quotient로 정의한 `JacobianQuotient`, `Module.length` 기반 `localLengthENat`.
- `Algebra.FormallyEtale/FormallyUnramified/FormallySmooth`, `Algebra.H1Cotangent`, `Ω[A⁄k]`, `Algebra.Extension.cotangentComplex`.
- `MvPolynomial.pderiv` Jacobian ideal, `Localization.AtPrime`(원점 국소환), `Polynomial.resultant`, `WeierstrassCurve.Δ/IsElliptic`, `ℤ_[p]`과 `hensels_lemma`.
- `SimpleGraph.edgeSet/ConnectedComponent/IsTree`, `PrimeSpectrum.basicOpen`, `widePullback`.
- univariate 경우에는 homological `H₁(L)`과 ann(f′) 사이의 다리(1717)까지 실제로 있다.

**다리 없는 proxy**
- étale bump는 `CurveFiber.bump : ℕ`이다. "realized" 버전 `etaleBumpT2`는 `H1FiberSpace := (Fin (2g) → k) × (Fin (b1+δ) → k)`(5778)로 *정의*되어 있어, `dim H¹ = 2g+b1+Σδ`가 구성에 의해 참이 된다. `ses_finrank`(5752) 자체는 진짜 rank–nullity이지만 자명하게 split된 곱에만 적용된다.
- motivic jump는 `motivicEulerJumpT2 := b1 + deltaSum`(6176)으로 답을 그대로 정의했다. defect motive는 `EulerComplexT2.defect` = (h0 = b1+δ, 0, 0)이다.
- δ-불변량은 임의의 `LocalDelta.delta : ℕ`이다. `quasihomogeneousCoprimeBranch`(812)는 δ = (m−1)(n−1)/2를 공식 그대로 넣은 것이다.
- dual graph는 `DualGraph.b1 : ℕ`이다. `SimpleGraphEuler`(6741)는 SimpleGraph에 대해서는 진짜지만, 곡선에서 그래프를 만드는 다리는 없다.
- τ는 조각별 표(604)다. 실제 대상과의 다리는 양쪽 다 나누어지는 행(⊤)에만 있다(5207). 유한 3행은 인스턴스 없는 인증서에 의존한다.
- `henselDx/henselDy/jacFullRankOffOrigin`(637–640)은 정의상 가약성(divisibility) 조건이다. 그래서 `gate_eq_jacobian`(644)은 `tauto`로 끝나는 명제논리 동어반복이다.
- `CurveModel.IsSmooth`는 정의상 b1=0 ∧ δ=0이다.
- 결론적으로 논문의 기하학적 대상(étale 코호몰로지, 모티브, 정규화, 스킴 코탄젠트 복합체)은 하나도 진짜로 정의되지 않았다. 파일도 이를 `paperCoverage`와 `remainingNativeObligations`(7313–7348)에서 인정한다.

## 6. 실질 수학 내용

**진짜이고 비자명한 증명**
- `PrincipalUnivariateAQ`(268–556): 주 conormal (f)/(f²) ≅ A, cotangentComplex = f′ 곱셈.
- `principalAQH1ModelEquivAlgebraH1Cotangent`(1717).
- `formallyEtale_iff_squarefree`(1799). 표준 étale 쌍과 `isReduced_of_field`를 쓴다.
- `kaehlerEquivJacobianQuotient`(1882): conormal 완전열과 Leibniz.
- `formallySmooth_of_grad_span_eq_top`(2179): `iff_split_injection` 위에 명시적 retraction을 세움.
- `resultant_map_derivative_of_monic`(3173): 차수가 떨어지는 경우를 `resultant_add_right_deg`로 처리.
- `benchSurface_jacobianQuotient_length_eq_top`(5163): `Bivariate.equivMvPolynomial`로 AdjoinRoot 모델에 옮겨 무한 길이를 보임.
- `originLocalTjurinaAlgebra_nontrivial_bothDivisible`(5324).
- `every_residue_root_lifts_uniquely_of_squarefree_reduction`(5714).
- `zero_hypersurface_grad_span_ne_top`(2349): 역방향이 f=0에서 거짓임을 정직하게 반례로 보임.
- `planeAQH1KernelModel_subsingleton_and_tjurina_not_subsingleton_of_isDomain`(2136).

**대략적 줄 비율 (주석 포함)**

| 구분 | 줄 수 | 비율 | 해당 블록 |
|---|---|---|---|
| 실질 수학 | 약 3,300 | 약 37% | 125–592, 1349–2416, 2788–3657 중 대부분, 4811–5374, 5541–5766, 6741–6846, 8481–8633 |
| 그중 비자명한 증명 | 약 1,800–2,200 | 약 20–25% | 위 블록 중 얇은 Mathlib 래퍼 제외 |
| 스캐폴딩 | 약 5,100 | 약 57% | 아래 목록 |

스캐폴딩 내역:
- `CurveModel` 515줄, `PaperFullFormalization` 370줄, `BypassCertificate` 964줄.
- `NormalizationReal`의 Fin 모델과 인증서 약 930줄, wiring 330줄.
- **`FullFormalizationAudit` 약 1,250줄**: `List String` ledger와 `….length = n := by decide` 정리 약 40개.
- `ReplacementTargets` 180줄, `DetectorPairData`/`TautologyFreeCurve` 약 245줄.

나머지(약 6%)는 헤더, imports, 예제다.

## 7. 수학적 정확성: 틀렸거나 과장된 진술

1. **`hensel_eq_discriminant` (746)**: 독스트링은 "a class admitting a unique ℤ_p-lift (Hensel gate)"라고 하지만 진술은 `Squarefree f ↔ IsCoprime f f'`이다. #6과 중복이며, Hensel 내용은 없다.
2. **`master_equivalence_curve` (981–986)**: 독스트링 "UNCONDITIONAL"은 과장이다(§4(a)2 참조). 헤더 117–119행의 "the strongest unconditional Lean layer possible"도 과장이다.
3. **`correctedResultantDiscriminantCertificate` (3314–3324)**: 독스트링은 "general-degree, non-monic case"라고 하지만 실제로는 `hF : F.Monic`을 요구한다.
4. **`grad_span_eq_top_of_formallySmooth_with_gradUnitCertificate` (2293)**: 가설 `_hfs`(formal smoothness)를 쓰지 않는다. 결론이 인증서 하나에서 나오므로 "reverse direction"이라는 프레이밍은 오해를 부른다.
5. **`unique_padic_lift` (5580)**: 독스트링은 "`∃!` packaging"이라고 하지만 실제로는 유일성을 버린다. 진술이 광고보다 약하다.
6. **`obstructionFree_iff_coprime` (589)**: `Iff.rfl`이다(Cor 2.11이라고 이름 붙음). `gate_eq_jacobian` (644)은 `tauto`다.
7. **헤더 75–77행**: `#print axioms`를 실행한다고 주장하지만 실제 섹션은 비어 있다(§3).
8. **ledger 내부 불일치**:
   - `EtaleChecklist.bumpChecklist`(7744), `MotiveChecklist`(7807), `SixFunctorBaseChangeChecklist`(7942), `DetectorSheafGluingChecklist`(8013), `NormalizationDataChecklist`(7873)이 `status := nativeMathlibTheorem`이다.
   - 같은 파일의 `paperCoverage`(7484–7493, 7559–7568)는 같은 대상을 `replacementTarget`/`certifiedInterface`로 정직하게 표기한다. 체크리스트 쪽이 과장이다.
   - 반대로 `cannotClaimCompleteNativeFormalization`(7353)과 `paperCoverage` 대부분의 메모는 정직하다. 다만 이 정리 자체는 리스트 리터럴에 대한 `simp`다.
9. **`nodalExample`의 "two nodes with δ = 3, 4"(1225)**: 표기 오류다.
10. **확인 불가 사항**: 벤치마크 `Model`(596)은 `pn`을 p와 독립인 자연수로 둔다. 논문의 x^{pn}이 p·n(같은 소수 p)을 뜻한다면 p∤pn 행은 결코 일어나지 않는다. 논문 원문을 볼 수 없어 판단을 보류한다.
11. **수학적으로 옳은 부분**: H¹(L)와 T¹의 분리, τ의 ∞ 정정, 쌍곡선 x^{pn}+y^A의 각 행 값((pn−1)(A−1), pn(A−1), (pn−1)A, ∞)은 표준 계산과 일치한다.

## 8. 코드 품질

- 장점:
  - 핵심 대수 계층은 증명이 깔끔하고 독스트링이 상세하다.
  - 깊은 Mathlib API(Extension.cotangentComplex, StandardEtalePair, resultant API)를 제대로 쓴다.
- 단점:
  - 8.9k줄 단일 파일에 5개 계층이 병합되어 있고, 계층마다 같은 개념을 재정의한다.
    - `Ideal.cotangentEquivOfEq`(137)와 `idealCotangentEquivOfEqKX`(404).
    - `derivativeMulLinearRaw`(444)와 `derivativeMulLinear`(1603).
    - `resultant_derivative_mod_eq_zero_iff_not_squarefree`(3211)와 `CompletionLayer.resultant_derivative_eq_zero_iff_not_squarefree`(4891).
    - `CurveModel.BaseChange`와 `NormalizationInputT2.BaseChange`.
  - 중복 래퍼가 많다.
    - `theorem_6_1`, `corollary_6_11`, `theorem_1_1`은 같은 정리다.
    - `theorem_2_1`, `proposition_2_7`, `proposition_3_11`, `proposition_3_31`, `proposition_5_5`는 모두 `X.base_change_identities`다.
    - `toArithmeticCurve_*` 45개는 이름 목록 `pastedCoverageWrapperNames`(7369)로 다시 나열되어 있다.
  - 약 1,250줄의 문자열 ledger와 빈 audit 섹션 19개가 있다.
  - 일반성이 부족하다. univariate 결과가 모두 `ZMod p`에만 서술되어 있는데, 완전체(perfect field)라면 어디서나 성립한다.
- **Mathlib PR 후보**(일반 체로 일반화한다는 전제): `Ideal.cotangentEquivOfEq`, `formallySmooth_of_grad_span_eq_top`, `kaehlerEquivJacobianQuotient`(Ω[k[X]/(f)] ≅ A/(f′)), `formallyEtale_iff_squarefree`(완전체), `resultant_map_derivative_of_monic`, `principalAQH1ModelEquivAlgebraH1Cotangent`(선형 동형으로 승격 권장, 현재는 `Equiv`).

## 9. 컴파일 위험

- `build-logs/`, `build-evidence/`, `evidence/`에 Spt2의 개별 성공/실패 기록은 없다.
  - `pr9-final-branch-health.txt`에는 Spt 언급이 없다.
  - `FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`는 13개 필수 파일 중 하나로 Spt2를 나열하고 "Until [15/15 PASS] exists, the project remains in progress"라고만 적고 있다.
  - CI workflow 여러 개(`primality-sheaf-verification.yml` 등)가 Spt2를 루트로 포함한다.
- 내가 확인한 것: 고정된 Mathlib 트리에서 덜 흔한 보조정리 이름 28개를 grep했다(`isRadical_iff_squarefree_of_ne_zero`, `resultant_add_right_deg`, `isCoprime_iff_aeval_ne_zero_of_isAlgClosed`, `equivH1CotangentOfFormallySmooth`, `range_kerCotangentToTensor`, `isTree_iff_connected_and_card`, `card_vert_le_card_edgeSet_add_one`, `IsTorsionBySet.isScalarTower`, `Bivariate.equivMvPolynomial`, `PadicInt.ker_toZMod` 등). 모두 존재한다. 이름 수준의 위험은 낮다.
- 취약할 수 있는 부분:
  - 긴 `rw`/`change`/`show` 체인(455–494, 1882–1975, 2179–2255).
  - 540행의 `synthInstance` heartbeat 상향.
  - Localization 몫에 대한 `Module (ZMod p)` 인스턴스 해석(5275).
- 종합하면 위험은 중간 이하로 보이지만 미검증이다. lead의 빌드 결과를 따를 것.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 8 | sorry/axiom/native_decide가 0이고 heartbeat 상향은 1건뿐이다. 다만 "#print axioms 실행" 주장은 사실이 아니고(빈 섹션 19개) 컴파일은 미검증이다. |
| 조건부 인증의 정직성(비순환성) | 3 | Master Equivalence의 모든 버전(`master_equivalence`, `CurveFiber`, `ArithmeticCurve`, `CertifiedSPT2`, `TautologyFreeCurve`)이 결론과 같은 필드나 가설에 의존한다. "UNCONDITIONAL"과 "TautologyFree"라는 이름은 오도적이다. `paperCoverage`와 `cannotClaimCompleteNativeFormalization`의 자기평가는 정직해서 감점을 일부 상쇄한다. |
| 수학적 실질성 | 5 | 대수 핵심(univariate 코탄젠트·étale·Kähler, 다변수 Jacobian 판정법 한 방향, resultant 환원, τ=⊤, Hensel)은 진짜이고 수준도 상당하다. 하지만 논문의 헤드라인(étale/모티브 검출기의 동치)은 전혀 형식화되지 않았다. |
| 정의 충실도 | 4 | 대수적 대상은 Mathlib의 실제 개념이다. 기하학적 대상(étale bump, H¹, motivic jump, δ, dual graph)은 답을 그대로 정의한 ℕ/`Fin n → k` proxy이고 진짜 개념과의 다리가 없다. |
| 코드 품질·유지보수성 | 5 | 핵심 증명은 깔끔하다. 그러나 단일 거대 파일에 계층 간 중복이 많고, 약 1,250줄의 문자열 ledger와 빈 audit 섹션이 있으며, `ZMod p`로 특수화되어 있다. |
| **종합** | **5** | 상당한 수준의 진짜 가환대수 형식화(약 20–25%)가 순환적 인증서 스캐폴딩(약 57%) 안에 묻혀 있다. "논문 정리 증명"이라는 라벨의 대부분은 필드 사영이다. |

---

## 커버리지 로그

원본 `.lean`을 순차적으로 Read한 범위:

- 1–700
- 700–1599(1600–1607의 일부 포함)
- 1600–2049
- 2050–2499
- 2500–3398
- 3399–4097
- 4098–4796
- 4797–5495
- 5496–6194
- 6195–6893
- 6894–7592
- 7593–8291
- 8292–8878 (EOF)

1–8878줄 전체를 읽었다. 건너뛴 범위는 없다. 반복적인 `toArithmeticCurve_*` 래퍼(4459–4726)와 문자열 ledger(7234–8452)는 읽기는 다 했고, 패턴이 단조로운 부분은 훑어 읽었다.

보조 작업:
- `decls_cls.json`에서 Spt2 선언 877개를 집계했다.
- grep으로 탈출구, `#print`, `set_option`, `instance`, 인증서 인스턴스화 위치를 확인했다.
- Mathlib 보조정리 이름 28개의 존재를 확인했다.
- build-logs/evidence에서 Spt2를 검색했다.
