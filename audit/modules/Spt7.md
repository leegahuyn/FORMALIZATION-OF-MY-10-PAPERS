# Spt7 감사 보고서 (`PrimalitySheafVerification/Spt7.lean`, 18,114줄)

감사 범위: 원본 `.lean` 1–18114줄 전부 (커버리지 로그는 맨 끝). lake/lean은 실행하지 않음. 단, `ModuleDepthDimensionInterface`의 모순성은 리드 감사자가 고정 Mathlib에 대해 Lean으로 **기계 검증**함(아래 §4).

선언 통계(decls_cls.json): theorem 950, def 371, abbrev 110, structure 124, inductive 6, instance 7, example 6. 접근자(accessor) 판정 theorem 203개(21%). 단, 접근자 판정은 필드 직접 사영만 잡으므로, 모순적 인터페이스 위에 세운 Prop .18 계열(약 160개)처럼 "합성된 사영"은 집계되지 않음 → 실제 비실질 비율은 훨씬 높음.

---

## 1. 목적·논문 대응

헤더(1–305줄): Lee Ga Hyun, "Section 4: Overlaps, Tor, Koszul Regularity, and Sheaf / Local Charts"의 형식화. 주장하는 대응:

- Thm .1 (4-층 독립성, canonical profile A=4, M=pₙ+3), T4-1 수치/p-진 Büchi 게이트, T4-2 타원곡선(EC) 층
- Thm .3/.19, Lem .6/.39, Cor .9/.40 (equalizer kernel = lcm, Čech Ĥ¹ ≅ ℤ/gcd, Tor₁ ≅ ℤ/gcd, Prop .7 CRT 분해)
- Thm .19(a) **정정**(min→max; 291–294줄에서 원 논문 오류를 명시)
- Prop .8 / Def .5 (IC = 지시 복잡도, |Tor| = exp(IC)), Cor .9 TFAE
- Lem .10/.14, Thm .11/.15, Prop .12/.16, Thm .17 (Koszul/정칙열)
- Prop .18 (depth 하한), Lem .37 (det–trace 형식 항등식), §6.2 Euler 곱
- Def .20/.21, Lem .22–.25/.29 (6-함자), Thm .30/Cor .27/.31 (층 Koszul), Lem .32 (곡선 축소), Prop .33/.41, Thm .34/.42, Cor .35, Lem .36, Prop .38, Prop .43, Thm .44, Cor .45/.46 (Weil II / Global Purity B), §7.2 검출자, **Thm .47 (Equivalence C, RH ⟺ TP)**, Standing .48
- 15800–15886줄 `paperStatementAliasRecords`가 .1–.48 전 항목에 별칭을 부여(문자열 레지스트리 + `rfl` 개수 정리).

헤더는 6-함자/Weil/Equivalence C를 "PROVED (interface)"로 표기하고 296–304줄에서 "étale cohomology가 Mathlib에 없어 conditional/omitted"라고 정직하게 밝힘. 다만 "PROVED" 표기 자체는 과장.

## 2. 헤드라인 정리 목록

| # | 줄 | Lean 이름 / 진술(요약) | 상태 |
|---|---|---|---|
| 1 | 2002 | `fourLayerStrictIndependence (P : FourLayerProfile)` : 각 층만 실패하는 무한 등차수열 4개 존재 | (U) — 단, 층 = "x ≡ 0 mod (쌍마다 서로소인 임의 법)"이라는 장난감 모델; CRT 한 줄짜리 |
| 2 | 372 | `canonical_coprime : p.Prime → 5 ≤ p → Coprime (p+3) (p^k)` | (U), 자명 |
| 3 | 2160 / 2382 | `cechPhiCokerEquivZModGcd : coker(ℤ→ℤ/M×ℤ/N) ≃+ ZMod (gcd M N)` / `arithmeticCechH1EquivZModGcd` | (U) 실질(구체 모델) |
| 4 | 2735 | `TorH1_iso_zmod_gcd : ker(×M on ZMod N) ≃+ ZMod (gcd N M)` (`card_ker_mulLeft` 2592 기반) | (U) 실질 |
| 5 | 14746 / 14738 | `abstractTorOneIsoGcd [NeZero M] [NeZero N] : ((CategoryTheory.Tor (ModuleCat ℤ) 1).obj (ZMod M)).obj (ZMod N) ≅ ModuleCat.of ℤ (ZMod (gcd M N))` (및 `Tor'`판) | **(U) — 진짜 Mathlib `Tor`와의 무조건 브리지.** `standardIntProjectiveResolution`(3103, QuasiIso 3090 증명) + `ProjectiveResolution.isoLeftDerivedObj` + 텐서 복합체 동형(3420/3456) + 호몰로지 이동(3681) |
| 6 | 2570 | `localized_intersection_prime_power_ideal_eq_span` : `((M)∩(p^k))` 국소화 = `span {p^max(v_p M, k)}` | (U) 실질, Thm .19(a) 정정판 |
| 7 | 4542 / 4567 | `cor9_tfae_gcd_tor_ic`, `arithmeticCechTorGate_tfae` : gcd=1 ⟺ |Čech|=1 ⟺ |TorH1|=1 ⟺ IC=0 | (U) |
| 8 | 4350 | `TorH1_primePowerDecomposition` (Prop .7 CRT 분해) | (U) |
| 9 | 4962 / 5033 | `koszulR2RightToCycles_range_eq_top_of_isWeaklyRegular_pair`, `koszulR2PositiveAcyclic_of_isWeaklyRegular_pair` (r=2 Koszul 중간 완전성) | (U) 실질 |
| 10 | 5302 | `koszulAcyclic_iff_isWeaklyRegular_of_interface` (Thm .11/.15) | (C/T) — 가정 `KoszulWeakAcyclicityInterface.cons`가 Koszul 판정법의 내용 그 자체; 증명은 리스트 귀납 한 번 |
| 11 | 7270 | `prop18_depth_lower_bound (D : ModuleDepthDimensionInterface R) : HasWeakRegularSequenceLength R M r → r ≤ D.depth M` | (C, **공허**) — 가정 구조체가 모순(§4), 게다가 결론 = 필드 |
| 12 | 8884 | `lem37_det_trace_formal_identity : det(1−XT)⁻¹ = exp(Σ tr(Tⁱ)/i·Xⁱ)` (Field K, ℚ-대수) | (U) **가장 실질적인 증명** (Jacobi 공식 8503/8561, 형식 ODE 유일성 8444) |
| 13 | 9173 | `quadraticEulerProductAt_hasProd_of_frobenius (D : FrobeniusRootDecomposition a α β) (hs : 1 < s.re)` | (C) 실질 — 입력 |α_p|=|β_p|=√p는 별개의 깊은 입력(SUBSTANTIVE) |
| 14 | 11459 | `thm44_globalPurityB_of_pure` (Global Purity B) | (A) 필드 사영의 조립 |
| 15 | 11952 | `equivalence_C (smooth) (der M pk) (Hder : der = 0 ↔ smooth) (Hgate : smooth ↔ gcd M pk = 1) : [gcd=1, smooth, der=0].TFAE` | **(T, 순환)** |
| 16 | 12028 / 12589 | `equivalence_C_faithful … (RH TP : Prop) (hRH : RH ↔ Gate) (hTP : TP ↔ Gate)`, `GlobalEquivalenceCBridge.rh_iff_tp` | **(T, 순환)** — "Riemann-hypothesis style statement"(11959)이 임의 `Prop` |
| 17 | 10138 | `thm30_sheafKoszul_positive_acyclic` | (A) = 필드 `positiveAcyclicOfRegular` |
| 18 | 16003 | `paper_thm19_originalMinIntersection_uncertifiable : ¬ paper_thm19_originalMinIntersectionClaim` (claim `:= False`) | (T) ¬False |

## 3. 탈출구 / 신뢰기반

- 주석 제거 후 `sorry`/`admit`/`axiom`/`native_decide`/`opaque`/`unsafe`/`implemented_by` 0 (리드 확인과 일치). `set_option maxHeartbeats` 상향 **없음**.
- `set_option linter.*` 6개 비활성(352–357줄: defProp, checkUnivs, unnecessarySimpa, unusedSimpArgs, unusedVariables, unusedTactic).
- 커스텀 `elab/macro/syntax` 없음. `#print axioms`는 16746–18111줄 약 1,366줄 **전부 주석 처리**되어 실제로는 아무 감사도 실행되지 않음(16070–16071 docstring이 "ordinary builds stay silent"라고 명시).
- `decide`는 작은 자연수 사실(15078–15087, 15056)뿐. `Inhabited False`류 트릭, `Classical.choice`로 데이터 날조 없음. `classical`은 `Fintype` 유도(954–963)에만.
- 인스턴스 7개: `tensorProductPUnitLeft/Right_subsingleton`(2771/2792, 정상 증명), `concreteECModPAffineSolutionsFintype`, `AddCommGroup` 재선언 3개, `principalCechPhi_range_normal` — 모두 무해.
- 취약점: 데이터(Iso)에 `simpa … using` 사용(3665, 14561, 14572, 14585, 14599) — 컴파일 취약성 요인(§9).

## 4. 조건부 인증 감사 (핵심)

### 4.1 (c) SUSPECT-VACUOUS → **증명 가능하게 모순 (기계 검증됨)**
- **`ModuleDepthDimensionInterface` (6709)** 및 **`ENatDepthDimensionAPI` (6775)**: `length_le_depth_of_isWeaklyRegular : ∀ {M : Type v} … {rs}, IsWeaklyRegular M rs → rs.length ≤ depth M`가 **모든** 가군에 대해 요구됨. 영가군 `PUnit`에서는 `IsSMulRegular`가 자명(부분단원 위 단사)이므로 `List.replicate n 0`이 임의 n에 대해 weakly regular → `n ≤ depth PUnit` (∀n) 모순. ℕ∞판은 `finite_eDepth`와 모순. **리드 감사자가 이 구조체를 그대로 복사해 `theorem interface_false (R) [CommRing R] (I : ModuleDepthDimensionInterface.{u,v} R) : False`가 고정 Mathlib에서 컴파일됨을 확인.**
  - 귀결: 6929–8350줄(약 1,400줄, theorem ~160개)의 `prop18_*` 전부, `ENatDepthDimensionInstantiationCertificate`(12870), `ActualDepthDimensionPackage`(12990, 필드 `api : ENatDepthDimensionAPI`), `ActualDepthDimensionInstantiationCertificate`(13057), `DepthCMLocalizationHandle.localizedDepthLowerBound`(14408) 등이 **공허하게 참**. 헤더 104–154줄의 "Prop .18 PROVED (interface)" 및 인벤토리 행 18은 실질 내용 0.
  - 동시에 (a) 순환이기도 함: `prop18_depth_lower_bound_of_isWeaklyRegular`(7262)는 필드 그 자체.

### 4.2 (a) CIRCULAR — 가설이 결론을 진술
- `equivalence_C` (11952): Hder, Hgate 두 동치를 받아 TFAE 출력 — Spt3의 `prime_iff_section_of_complete`와 동일 패턴.
- `equivalence_C_faithful_tfae` (11962), `equivalence_C_faithful` (12028), `equivalence_C_faithful_rh_iff_tp` (12044), `equivalence_C_faithful_localRH_tfae` (12443), `GlobalEquivalenceCBridge` (12561; 필드 `RH TP : Prop`, `rh_iff_global`, `global_iff_local`, `tp_iff_tracePurity`) → `rh_iff_tp` (12589). "RH ⟺ TP"는 가정된 두 동치의 추이성일 뿐.
- `DetTraceRadiusCertificate` (11031): `hasDetTraceExpansion`, `radiusLimit`가 임의 Prop, `radius_of_bound`가 곧 Prop .38. `radiusLimit := fun _ _ => True`로 즉시 인스턴스화 가능 → `prop38_radius_limit_of_pure/mixed`(11059/11069), Cor .45 공허.
- `SheafKoszulModel` (10005): `positiveAcyclicOfRegular` = Thm .30; `rs : List ℕ`(환 원소가 아님!). `SheafKoszulChartwiseCertificate.sheafRegular_of_chartwise` (10225) = Cor .31.
- `OpenClosedWeightControl` (10802): 2-out-of-3 필드 = Cor .35.
- `GrothendieckLefschetzPackage` (11136): `pointCount` 임의 함수, `traceFormula` 필드 = Lem .36 (pointCount를 교대합으로 정의하면 자명 인스턴스).
- `FiniteSupportCohomologyVanishing` (11329): `cohomology : ℕ → Type*` 임의, `positiveSubsingleton` 필드 = Prop .43; `finiteSupport : Prop` 임의.
- `DetectorPackage` (11575): §7.2 모든 진술이 필드.
- `KoszulWeakAcyclicityInterface`/`KoszulRegularAcyclicityInterface` (5291/6513): cons 법칙 = Koszul 판정법. `KoszulComplexModel` (5381)의 `acyclic`은 `complex`의 호몰로지와 **아무 연결 없음**; 유일한 인스턴스 `lowDegreeKoszulComplexModel` (5458)은 `acyclic := IsWeaklyRegular`(동어반복), 길이 0 및 ≥3에서 `complex`는 `koszulR1ChainComplex 0`이라는 엉뚱한 자리표시자(5437–5443).
- `LocalRHWeightCertificate.pure_iff_frobenius_radius` (12379): 역방향(local RH ⇒ purity)을 가정.
- `CechCRTRefinementHypothesis` (4215) ≡ `CechCRTRefinementCertificate` (4230): 필드 동일, "인증서"는 가설의 재포장.

### 4.3 공허한 라벨 / 자유 Prop 플래그
- `PadicLogBridgeCertificate` (1390), `PadicABLogTruncationCertificate` (1464), `ActualPadicLogTruncationPackage` (1584): `LogBound`, `logOnePlus`, `LogExpr`가 전부 임의 → `LogBound := fun _ => True`로 자명. p-진 로그는 어디에도 정의되지 않음.
- `PadicCompletionComparison` (4192): `isCompletion : Prop` 하나뿐(제약 없음, `False`도 가능).
- `Actual*Package`들(9831 6-함자, 9891 Def21, 13323 Koszul, 13543 EC, 13772 derived Čech–Tor, 14037 Weil/trace, 14115 Global Equivalence C): "…Available : Prop" 필드와 그 연언 증명 — `True`로 즉시 충족, 의미 없음.
- `Def21ActualSheafConstructionGap` (9731)/`def21ActualSheafConstructionGap` (9799) 및 `GeneralKoszulBridgeChecklist` (13283/13301): 플래그를 `False`로 두고 "unavailable"을 `¬False`로 증명 → `def21_actual_constructor_unavailable` (9823)은 동어반복.
- `SixFunctorData` (9286): `Sch`는 임의 범주, `Sheaf`/`IsConstr`/`SheafIso`/`distinguished` 전부 임의 → `PUnit`/`True`로 자명 인스턴스. Lem .22–.25/.29 및 `CurveFactorization`(10340, Lem .32) 결과는 필드 조합.
- `WeilIIPackage` (10541): `frobEigenvalues : ℕ → Set ℂ` 임의, F와 무관(빈 집합이면 자명). `ECWeilICompatibility.weightOneRadius_eq_sqrt` (10647)는 `q_eq_primeCard`로부터 유도 가능한 잉여 필드.

### 4.4 (b) SUBSTANTIVE (깊지만 분리가 깔끔한 입력)
- `HasseBoundCertificate` (1041): Hasse 부등식(참인 정리; 현재 Mathlib에 없음). `ECJacobianHenselSmoothCertificate` (878)의 discriminant⟺IsElliptic, affineSmooth⟺discriminant는 (p 소수일 때) 참으로 보이며 원칙상 증명 가능. `ECOrdSSTagCertificate` (1016) 건전.
- `TorBaseChangeNaturalityHypothesis` (4136): 평탄 R에서 참일 개연성. 단 `torFlatBaseChangeNaturalityCertificate` (4175)는 `[Module.Flat ℤ R]`을 받고도 쓰지 않음(평탄성이 아무것도 방출하지 않음).
- `FrobeniusRootDecomposition` (9039): |α|=|β|=√p (EC에선 Hasse, 일반적으론 Weil). 이 위의 Euler 곱 수렴 증명은 진짜.

### 4.5 (d) DISCHARGED
- 산술 핵심 전부: `ArithmeticCechTorGate` (4550) ⟸ gcd=1 (4554), Standing .48 `canonicalCechTorSilent` (15438), `PresheafCechSkeletonCertificate`(12791), `StandardFreeResolutionTorComparison`(3746), `ConcreteTorMathlibCertifiedBridge`(14977) 등 "canonical" 인스턴스는 실제 증명된 정리로 채워짐.
- Mathlib 추상 Tor 비교: 14581–14750에서 **완전히 방출됨**(§2 #5).

### 4.6 참조 인스턴스
Mock1_Advanced식 "0/자명 데이터 인스턴스"는 **없음**. 대신 깊은 인터페이스(SixFunctorData, WeilIIPackage, GL, DetectorPackage, Hasse, PadicLog, depth API 등)에 대한 **닫힌 인스턴스가 하나도 없음** → 비공허성이 전혀 입증되지 않았고, depth 인터페이스는 아예 모순. 유일한 예시 인스턴스는 `exampleFourLayerProfile`(2,3,5,7; 15073)과 동어반복 `lowDegreeKoszulComplexModel`.

## 5. 정의 충실도

- **Tor₁**: `TorH1 M N := ker(×M on ZMod N)` (2724)는 프록시지만, `abstractTorOneIsoGcd`(14746)로 Mathlib `CategoryTheory.Tor`에 **연결됨** — 모범적. (단, `MathlibTorOneEndpointHandle.comparisonStatus := abstractDerivedFunctorEndpointPending`(14620), `ConcreteTorMathlibBridge`(14961), 14577–14580 docstring은 "미완"이라고 낡은 상태를 표기 → 스스로를 과소평가하는 불일치.)
- **Čech/층**: `arithmeticCech*`는 Mathlib `PrimeSpectrum.basicOpen` D(M), D(N)을 **라벨로만** 사용하고, 그 위 "섹션"으로 ZMod M, ZMod N, ZMod gcd를 둠. 실제로 D(M)의 구조층 섹션은 ℤ[1/M]이고 ℤ/M은 닫힌 V(M)의 좌표환 → 열린집합–섹션 대응이 수학적으로 어긋남. `ArithmeticTwoOpenCechSheafCertificate`(2398)의 `leftOpen` 등은 군들과 아무 관계식이 없음. `arithmeticConstantIntPresheaf`(555)/`arithmeticPredicatePresheaf`(618)는 항등 제한을 갖는 상수 전층(층 조건 미증명), `arithmeticIntFunctionSheaf`(570)는 Mathlib의 `sheafToType`으로 진짜 층이나 Čech 계산과 연결되지 않음. Mathlib의 Čech 코호몰로지와의 브리지 없음.
- **4-층 게이트**: `Fnum/Fmod/Fp_adic/FEC`(516–525) = 단순 합동식; p-진 로그·모듈러 형식·Hensel은 모델되지 않음. `ECConcreteLayerProfile`(1108)은 `ecMod = p`만 요구.
- **EC**: Mathlib `WeierstrassCurve`로 충실히 정의(739–783). 다만 `a₄ = −pⁿ`이 mod p에서 0이 되므로(n≥1) 축소곡선은 실질적으로 y²=x³−A.
- **p-진 수치 게이트**: `padicValInt`, `ℤ_[p]` ideal로 충실(1257–1348). p-진 로그 자체는 정의 안 됨.
- **Koszul**: r=1,2는 Mathlib `ChainComplex (ModuleCat R)`로 충실, 호몰로지는 구체 ker/range 몫(Mathlib `homology`와 연결 안 됨). 임의 길이는 외대수 미분 d²=0 코어(5543–5604)와 기저 변환 동형(6100–6125)까지만; 호몰로지/판정법은 미형식화.
- **regular sequence / flat base change**: Mathlib `IsWeaklyRegular`, `IsRegular`의 재포장(6572–6655) — 충실.
- **depth/CM**: Mathlib 정의 없이 모순적 인터페이스로 대체.
- **6-함자/étale/weight/RH**: 전부 임의 타입·Prop 필드 — 실제 대상과의 브리지 없음.

## 6. 실질 수학 내용

진짜 논증(비자명, Mathlib 실사용):
- CRT/Čech: `crt_solvable_iff`(2030), `crtDel_exact_crtPhi`(2108), `cechPhiCokerEquivZModGcd`(2160), 임의 환 R 기저변환 판 `principalCechPhi_range_eq_principalCechDel_ker`(3903), 자연성 `cechCokerBaseChange_naturality_mk`(4046).
- `card_ker_mulLeft`(2592), `ker_mulLeft_le_zmultiples_generator`(2681), `zmodGcdEquivKerMulLeft`(2699), `TorH1_primePowerDecomposition`(4350), `gcd_eq_prod_primeFactors`(4386), `card_Tor_eq_exp_IC`(4432), `IC_mono`(4440), `IC_coprime_add`(4486).
- `localized_lcm_prime_power_ideal_eq_span`(2536).
- `standardIntResolutionAugmentation_quasiIso_of_ne_zero`(3090) → `standardIntProjectiveResolution`(3103); `zmodLeftUnitor_comp_zmodMulLeftModuleHom`(3350); `tensorRightStandardResolutionComplexIso`(3420); `tensorStandardResolutionActualHomologyOneIsoStandardEndpoint`(3681); `abstractTorOneIsoGcd`(14746).
- Koszul r=2 중간 완전성(4962), 외대수 기저변환 사슬사상(5983, 6040), r=2 기저변환 미분(6355–6395).
- det–trace: `powerSeries_eq_of_derivative_eq_mul`(8444), `derivative_det_eq_sum_updateCol`(8503), `derivative_det_oneSubXMatrix`(8619), `oneSubXMatrix_mul_psMatrixOfPowers`(8674), `inv_det_smul_adjugate_oneSubXMatrix_eq_psMatrixOfPowers`(8735), `lem37_det_trace_formal_identity`(8884).
- Euler 곱: `frobeniusLinearEuler_hasProd_of_abs`(9135), `quadraticEulerProductAt_hasProd_of_frobenius`(9173).
- 국소 RH 반지름: `localListZerosOnCircle_iff_localEigenvalueListOnCircle`(12194) — 초등적이지만 정확.

대략적 줄 비율(18,114줄 기준, 추정):
- 실질 수학 ≈ 25% (§A 일부 ~600, §B ~1,800, §D ~1,200, §F/G ~800, §K Tor 브리지 ~150, 국소 RH ~150 ≈ 4,700줄). 그중 "깊은" 증명은 ~10%.
- 공허(모순 인터페이스) Prop .18: ~1,700줄(≈9%).
- 필드 사영/순환 인터페이스(§H 6-함자·Weil·GL, §I Equivalence C, 검출자): ~3,400줄(≈19%).
- 체크리스트/핸들/Actual*Package/재포장: ~2,300줄(≈13%).
- 논문 인벤토리·문자열 레지스트리·`rfl` 개수: ~1,700줄(≈9%).
- 주석 처리된 `#print axioms`: ~1,370줄(≈8%), 헤더/docstring/공백 나머지.
→ **실질 ≈ 25%, 비실질(스캐폴딩·사영·공허) ≈ 75%.**

## 7. 수학적 정확성

- 거짓 진술은 발견 못함(공허 참은 있음). Thm .19(a) 정정(max vs min)은 올바르고 증명됨(2492/2570) — 칭찬할 점.
- 그러나 원 min 진술을 반증하지는 않음: `paper_thm19_originalMinIntersectionClaim : Prop := False`(15998), `…_uncertifiable : ¬False`(16003). 반례(M=p, k=2 등)는 쉽게 형식화 가능했음.
- 과장된 docstring:
  - `equivalence_C`(11949–11951) "판별식 게이트, 유도 검사, equalizer 면이 동치이다" — 실제로는 두 동치를 가정.
  - `equivalence_C_faithful_tfae`(11959) "Riemann-hypothesis style statement" — RH는 임의 `Prop`.
  - `prop18_depth_lower_bound_of_isWeaklyRegular`(7260) "every depth API satisfying…" — 그런 API는 존재 불가.
  - 헤더 "Thm .1 … PROVED" — 장난감 합동 모델에 대한 CRT.
  - `arithmeticCech*` "two-open sheaf condition"(2184–2189, 2294) — 실제 층 조건이 아님(§5).
  - `def21_actual_constructor_unavailable`(9823), `GeneralKoszulBridgeChecklist`의 "unavailable" — `¬False`.
- 낡은 상태 표기: `abstractDerivedFunctorEndpointPending`(14620, 14867, 14896, 14937, 14961) vs 실제 완료(14738/14746) — 오히려 과소진술.
- `SheafKoszulModel`의 `rs : List ℕ`(10007) — 계수환 원소가 아니라 자연수 리스트, 의미 불명.

## 8. 코드 품질

- 18k줄 단일 파일, 거대한 중복: Prop .18 변형 ~150개(같은 사실을 `koszulAcyclic`/`koszulRegularAcyclic`/`koszulModel`/`lowDegree`/`flat`/`faithfullyFlat`/`localized` × `isCohenMacaulay`/`depth_eq_dimension`/`eDepth` 조합으로 반복), 체크리스트 구조체가 다른 체크리스트를 다시 묶는 다층 래핑(`MathlibGapWorkaroundChecklist`(14264) ⊃ `CoreRemainingFormalizationChecklist`(13994) ⊃ …), 문자열 레지스트리와 `rfl` 개수 정리, 1,370줄 주석 처리된 `#print axioms`.
- 헤더 272–273줄 인코딩 손상("짠K", "??").
- 린터 6종 비활성. 이름은 대체로 일관적이나 `paper_*` 별칭이 `abbrev := @…`로 대량 중복.
- **Mathlib PR 후보(가치 있음)**: `abstractTorOneIsoGcd`(Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd) + `standardIntProjectiveResolution`; `derivative_det_eq_sum_updateCol`/`derivative_det_oneSubXMatrix`(다항식 행렬 Jacobi 공식); `powerSeries_eq_of_derivative_eq_mul`; `lem37_det_trace_formal_identity`(det(1−XT)⁻¹ = exp Σ tr Tᵏ Xᵏ/k); `card_ker_mulLeft`/`zmodGcdEquivKerMulLeft`; r=2 Koszul 완전성; `localized_lcm_prime_power_ideal_eq_span`.

## 9. 컴파일 위험

- `build-logs/`, `build-evidence/`, `evidence/`에 Spt7 고유 컴파일 로그 없음(`FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`에 대상 파일로만 열거). `pr9-final-branch-health.txt`의 오류는 Mock2_FunctionalAnalysis 전용, Spt7 언급 없음 → **컴파일 상태 미확인**(리드의 별도 빌드에 의존).
- 리드가 `ModuleDepthDimensionInterface` 복사본을 고정 Mathlib에서 컴파일한 것은 해당 import·API 이름이 유효함을 부분적으로 시사.
- 위험 요인: 데이터(Iso)에 `simpa using`(3665, 14561, 14572, 14585, 14599); `ModuleCat.hom_hom_leftUnitor`, `ModuleCat.hom_whiskerRight`(3366–3367) 등 버전 민감 API; `ChainComplex.of_d`/`homologyIsoSc'` 기반 `change` 다수; universe 매개변수 12개짜리 구조체(14264, 16100) — elaboration 부담. heartbeat 상향이 없으므로 통과한다면 비교적 가벼운 파일일 것.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 7 | sorry/axiom 0, 트릭 없음; 단 컴파일 미확인·data `simpa` 취약 |
| 조건부 인증의 정직성(비순환성) | 3 | 산술 핵심은 무조건이나, Thm .47 순환, Prop .18 인터페이스 **모순(기계 검증)**, §H–§I 결론=필드, 자유 Prop 플래그 남발, "PROVED (interface)" 표기 |
| 수학적 실질성 | 5 | Tor₁↔Mathlib Tor 브리지, Čech/CRT, det–trace/Jacobi, r=2 Koszul, Euler 곱은 진짜; 전체의 ~25% |
| 정의 충실도 | 5 | Tor·정칙열·Weierstrass·padicVal은 충실; Čech "층"은 라벨 불일치, p-진 로그·depth·6-함자·weight는 임의 필드 |
| 코드 품질·유지보수성 | 3 | 18k줄 중 ~75% 스캐폴딩, 대량 중복, 낡은 상태 태그, 주석 1,370줄; 일부 Mathlib PR급 보조정리 |
| **종합** | **4** | 견고한 산술/호몰로지 핵심(특히 abstract Tor₁ ≅ ℤ/gcd) 위에 순환·공허한 대규모 인터페이스 층 |

---

## 커버리지 로그

| 줄 범위 | 방식 |
|---|---|
| 1–1000 | Read 전문 |
| 1000–1999 | Read 전문 |
| 1999–2998 | Read 전문 |
| 2999–3998 | Read 전문 |
| 3999–4998 | Read 전문 |
| 4999–5998 | Read 전문 |
| 5999–6998 | Read 전문 |
| 6999–7848 | Read 전문 (Prop .18 반복 변형은 구조 확인 위주로 훑음) |
| 7849–8648 | Read 전문 (7849–8350 Prop .18 ℕ∞ 변형 훑음) |
| 8649–9448 | Read 전문 |
| 9449–10298 | Read 전문 |
| 10299–11148 | Read 전문 |
| 11149–11998 | Read 전문 |
| 11999–12848 | Read 전문 |
| 12849–13698 | Read 전문 |
| 13699–14548 | Read 전문 |
| 14549–15398 | Read 전문 |
| 15399–16298 | Read 전문 |
| 16299–17248 | Read 전문 (16746–17248은 `-- #print axioms` 주석) |
| 17249–18111 | `sed`+`grep -v "^-- #print axioms "`로 기계 확인: 863줄 전부 주석 `#print axioms` (비주석 줄 0) |
| 18112–18114 | `end AxiomAudit`, `end Spt7` 확인 |

보조 자료: `scan/Spt7.code.lean`, `scan/decls_cls.json`(섹션별 통계), Mathlib `RegularSequence.lean`/`Regular/SMul.lean`(공허성 논증 확인). 작업 노트: `reports/Spt7_notes.txt`.
