# Mock2_FunctionalAnalysis — Part 2 범위 감사 (lines 15900–31600)

감사 범위: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean` 15900–31600 (15,701줄; 실제로는 31619까지 읽음).
선행 노트: `reports/FA_notes.txt` (1–15899). repo 수정·lake 실행 없음.

범위 통계 (주석 제거본 기준): 코드 12,266줄 / 주석 1,873줄 / 공백 1,562줄. `#print axioms` 384줄, `#synth` 4줄. 선언 1,243개 (theorem 915, def 270, instance 31, abbrev 22, structure 5). decls JSON 의 accessor 플래그 1개뿐 → 앞 모듈들(Mock1_Advanced 등)의 "필드 투영 정리 대량생산" 패턴은 **이 구간에 없다**.

---

## 0. 구간이 다루는 수학 (요약)

1. (15900–16184) ambient `C_c^∞(ℍ)` 코어(Mathlib `TestFunction`) 위 raising/lowering Green 항등식 마무리 및 raw 연산자로의 브리지.
2. (16186–16484) `GammaTwoQuotientGreenBoundary`: 몫 Stokes 를 위한 정확한 "누락 명제"를 Prop 으로 명시 (flux one-form, Γ(2) pullback 불변성, cusp tail, paired-polygon Stokes).
3. (16486–19902) `DefinitionOneSobolev`: 실제 Petersson 내적(몫 측도 적분) → 내적 공간 → Hilbert 완비화; 논문 Definition 1 의 그래프 노름 `‖u‖²+‖Ru‖²+‖Lu‖²` 완비화(`SobolevCompletion`, `GraphSobolevCompletion`).
4. (19906–21325) `ExplicitDiscriminantPotential`: Mathlib 판별식 Δ 의 Petersson 밀도 `VΔ = ‖conj Δ·Δ·y¹²‖` 를 실제 퍼텐셜로 사용 (양성·불변·유계·cusp 감쇠), 불변 bump, 유계 퍼텐셜 연산자.
5. (21327–22291) `CompactSeparableKernelPotential`: VΔ 곱셈의 콤팩트성 대신 rank-one 커널 `|φ⟩⟨φ|` 사용 + 장난감 Fredholm 모델.
6. (22293–23804) `FixedPhaseDensity`: 고정위상 안정 코어 = 전체 smooth compact 공변 코어, 불변 cusp-cutoff 분할, 무한차원성.
7. (23806–26150) `FixedPhaseClosedOperators`: Petersson 완비화의 구체 `Lp` 실현, 국소 분포론으로 R/L 의 **무조건 닫힘가능성**, T†† = closure.
8. (26152–26479) `#print axioms` 318줄.
9. (26495–27165) 모든 정수 지수에서 비영 코어 원소.
10. (27167–28299) 이중 수반 = 닫힘, Definition-1 그래프 완비화 JointlyClosable, 완비화 위 Green, strong cross-adjoint ⇔ essential core.
11. (28300–31362) P3.4: 6-타일 분해, 곡선 타일 Green 정리(Piola + Jacobian), Möbius–Piola 수송, Mathlib `curveIntegral`, 짝지어진 변 소거, 변 짝짓기 involution.
12. (31364–31494) essential core ⇔ 순차 그래프 근사 (Friedrichs/Gaffney 입력을 명시).
13. (31498–31619) 기본 변의 ambient 매개화와 실제 도함수 (다음 구간으로 이어짐).

**구 CI 오류 구간 18908–19748** 의 수학적 내용: `QuotientHilbertCoordinates` 의 완비화 계층 — `graphExtension`(등거리 확장), `range_graphExtension_eq_closure_range_graph`, base/raise/lower 연속 사영, `completionEnergyOperator`(= `innerSLFlip`, 상수 1 Lax–Milgram/Riesz), `JointlyClosable`/`closedRaise`, `energyCompletionMap` 과 `denseRange_iff_surjective_energyCompletionIsometry`, `CompatibleCoreInclusion`, `TypedDifferentialAdapter`(레거시 `ExponentIndexedDifferentialCore` 어댑터), `FixedPhaseGraphCompletion` 의 인스턴스 재노출. 18748–18752·18770–18776 주석과 `#synth` smoke test 가 "의존 abbrev 를 통한 비싼 typeclass 탐색 실패"를 명시적으로 회피하고 있어, 과거 오류가 수학이 아니라 **인스턴스 elaboration 문제**였음을 시사한다 (현재는 컴파일됨). 수학적으로는 표준적·일반적 함수해석(그래프 노름 완비화)이다.

---

## 2. 헤드라인 정리 (범위 내)

| # | 줄 | 이름 | 내용(요약) | 상태 |
|---|---|---|---|---|
| 1 | 15959 (+15894 앞구간) | `compact_lowering_green_identity` | ambient `C_c^∞` 코어에서 `⟨y^{a/2}·conj(L̃u), v⟩ = −⟨…u, R_a v⟩` (Mathlib IBP) | U |
| 2 | 17117 | `peterssonForm_self_eq_zero_iff` | `peterssonForm M D u u = 0 ↔ u = 0` (IsOpenPosMeasure + `Measure.eq_of_ae_eq`) | U |
| 3 | 17997, 18072 | `greenBoundaryDefect_eq_integral_fixedPhaseGreenFlux`, `fixedPhaseGreenFlux_invariant` | 실제 Petersson Green 결함 = 명시적 flux 발산 적분; flux 가 Möbius pullback 불변 | U |
| 4 | 18391 | `greenBoundaryDefect_eq_zero_of_pairedPolygon` | `GammaTwoPairedPolygonFluxStokes → greenBoundaryDefect n u v = 0` | C (가설은 33349 `gammaTwoPairedPolygonFluxStokes` 에서 해소 → 사실상 U) |
| 5 | 19954, 20029, 20064 | `upstairsPotential_pos`, `exists_uniformBound`, `upstairsPotential_isZeroAtImInfty` | 실제 Δ-퍼텐셜: 양성·유계·cusp 감쇠 (Mathlib modular forms) | U |
| 6 | 20560, 27125 | `compactInverseEtaPaperCore_ne_zero`, `compactInverseEtaFixedPhaseCoreAllIndex_ne_zero` | 실제 비영 smooth 몫-콤팩트 반정수 weight 단면 (bump·η⁻¹·Wirtinger 인자), 모든 n | U |
| 7 | 23795 | `inverseEtaFixedPhaseCoreZero_not_finiteDimensional` | 물리 코어 무한차원 (서로소 shell 의 선형독립 가족) | U |
| 8 | 21171, 21298 | `norm_peterssonPotentialOperator_le_uniformBound`, `graphPotentialOperator_bound` | VΔ 퍼텐셜 형식의 완비화 위 유계성 (Cauchy–Schwarz 경유) | U |
| 9 | 25633, 25703, 26142 | `physicalRaise_isClosable`, `physicalLowerFromSucc_isClosable`, `all_physical_operators_closable` | Green 가설 **없이** 국소 분포 유일성으로 R/L/joint 닫힘가능성 | U (본 구간 핵심) |
| 10 | 25209, 25307 | `submodule_adjoint_adjoint_eq_topologicalClosure`, `adjoint_adjoint_eq_closure` | 일반 Hilbert 공간: `T†† = T.closure` (Mathlib 미보유) | U, upstream 후보 |
| 11 | 27649, 27612 | `coordinates_jointlyClosable`, `successorGraphUnwrap_image_range_graphExtension_eq_closedJointGraph` | Definition-1 그래프 완비화의 base 사영 단사, 완비 그래프 = 닫힌 joint 연산자 그래프 | U |
| 12 | 28033 | `graphSobolevGreenDefect_eq_zero` | 완비화된 그래프 영역 전체에서 Green 항등식 | C (`PhysicalGreenIdentityAt`; 33398 에서 해소) |
| 13 | 29863 | `setIntegral_heightSq_divergence_modularClosedTile_eq_boundary` | 절단된 표준 modular 타일 위 곡선 Green 정리 (Piola + Mathlib Jacobian + 직사각형 발산정리) | U (실질적, 비자명) |
| 14 | 30485, 30659 | `divergence_selectedCosetPiola`, `integral_heightSq_divergence_selectedHalfOpenTile_eq_basePiola` | Möbius Piola 항등식 `div(Piola) = |det DΦ|·div∘Φ` (Cauchy–Riemann 소거), 타일 수송 | U |
| 15 | 31143, 31070 | `GammaTwoActualPolygonEdge.paired_paired`, `invariantFlux_actualPairedEdge_integral_cancel` | 변 짝짓기는 involution (Γ(2) 정규성), 짝 변 적분 소거 | U |
| 16 | 21862 | `explicitUnshiftedFredholmData` | `A = I − P`, `S = I` 장난감 Fredholm 데이터 | T (모델) |
| 17 | 19881 | `pageFourHOneEquivPageTwelveGraph` | `LinearIsometryEquiv.refl` — 두 이름이 같은 타입 | T |

---

## 4. 조건부 인증 감사 (범위 내 명명 가설·인증서)

| 이름 (줄) | 성격 | 분류 | 비고 |
|---|---|---|---|
| `GammaTwoClosedCarrierCompactPreimage` (16297) | 몫 콤팩트 ⇒ carrier 역상 콤팩트 | **DISCHARGED** 16304 | 앞 구간 정리 재사용 |
| `GammaTwoQuotientCompactFluxTailTightness` (16310) | 몫-콤팩트 flux 는 F_Y 밖에서 0 | **DISCHARGED** 16351 (증명 16318, genuine) | |
| `GammaTwoPairedPolygonFluxStokes` (16363) | 6-타일 다각형 Stokes | 범위 내 SUBSTANTIVE; **DISCHARGED** 33349 (`gammaTwoPairedPolygonFluxStokes`, Part 3 범위) | 진술은 그럴듯하고 비공허(실제 비영 flux 가 가정 충족). 증명 검증은 Part 3 몫 |
| `GammaTwoCompactFluxStokes` (16376) | 결합 Stokes | **DISCHARGED** 33373 | |
| `FixedPhaseGreenFluxBridgeStatement` (18325) | 결함 = 발산 적분 + 정칙성 | **DISCHARGED** 18346 | "결과를 가정" 아님 — 정직 |
| `IsGammaTwoInvariantFlux`/`IsSmoothQuotientCompactFlux`/`HasZeroThreeCuspTail` | 술어 | 실제 flux 에 대해 **DISCHARGED** (18313, 27812) | |
| `EnergyDefinite` (18661), `JointlyClosable` (19126) | 술어 | 실제 좌표에 대해 **DISCHARGED** (19695, 27649) | |
| `PhysicalGreenIdentityAt`/`PhysicalGreenIdentity` (25478/25484) | `greenBoundaryDefect = 0` | 형식상 **CIRCULAR** (예: 27863 `physicalRaisingGreenIdentityOnCore` 는 가설을 `eq_neg_iff_add_eq_zero` 로 재진술할 뿐) — 그러나 **DISCHARGED** 33398/33404 (`physicalGreenIdentity_unconditional`) | 범위 내 `…_of_green` 정리들은 최종적으로 무조건이 됨 |
| `IsEssentialGraphCoreFor`, `RaisingEssentialAdjointCoreAt`, `LoweringEssentialAdjointCoreAt`, `StrongCrossAdjointAt`, `…HasPhysicalCoreAt` (28066–28139), `HasSequentialGraphCore`, `…SequentialApproximationAt` (31397–31446) | essential self-adjoint 류 입력 | 범위 내에선 동치 관계만 증명 (U-동치). 28271 `strongCrossAdjointAt_of_pairedPolygon_of_reverseInclusions` 는 역포함(= Green 하에서 결론과 동치)을 가설로 받음 → **CIRCULAR-형** 이나 문서가 정직히 "missing input"이라 표기. `StrongCrossAdjointAt` 는 37566/37586/63073 에서 해소되는 것으로 보임 (Part 3/4 검증 필요) | |
| `hShift : ComplexCoerciveWith α (shiftedForm …)`, `hker` (21539, 22149) | 이동된 형식의 강압성 | **SUBSTANTIVE**, 범위 내 미해소 | 실제 해석적 핵심 |
| `hS : S = A + λ·rankOne` (21559, 22162) | 분해 | 범위 내에선 장난감 모델(21862)에서만 해소 | |
| `DenseRange (graphRangeIsometry …)` (19444 `completionEquiv`) | 두 코어 그래프 밀도 | C, 그러나 주 라인에선 "한 코어" 설계로 회피 | |
| `ThreeWeightHilbertRealization` (19479) + `PaperExponentIndexedDifferentialCore` (앞구간 15129) | 레거시 인터페이스 | 범위 내 **미인스턴스** (19573–19628 결과는 C) | 다른 잉여류 코어를 ⊥ 로 두면 거주 가능해 보이나 확인 안 함 (불확실). 주 라인에서 사용 안 함 — dead end |
| `SesquilinearCuspTailControl` 인스턴스들 | cusp tail 인증서 | **DEGENERATE**: `constantCompactCuspTail` (21464) 이 `truncation := C`, `epsilon := 0` 으로 채움; `rankOneCuspTail`, `pulledBackKernelCuspTail`, `explicitCompactKernelCuspTail`, `graphBaseKernelCuspTail`, `compactCoreKernelCuspTail` 모두 동일 | 연산자가 이미 콤팩트라 수학적으로 참이지만 cusp 기하 정보 0 |

**reference/example 인스턴스 평가**: 이 구간의 구체 인스턴스는 대부분 **실제 객체**를 담는다 — Δ 판별식(Mathlib `discriminantCuspForm`), η⁻¹ 단면, 비영 bump, 실제 Petersson 측도, 실제 Möbius 미분. 예외는 (i) cusp-tail 인증서의 상수 절단(위), (ii) rank-one "compact potential" 대체물, (iii) `I − P` 장난감 Fredholm 모델, (iv) 정의상 refl 인 page4/page12 동일시.

---

## 5. 정의 충실도

- **Petersson 내적** (16961 `peterssonForm`): 높이 보정 fiber 계량 `y^{k/2}|f|²` 의 불변 밀도를 몫으로 내려 `D.quotientMeasure`(Mathlib `volume` on ℍ 기반 기본영역 측도) 로 적분. 기본영역 독립성(17007) 증명. **충실**.
- **L²**: `PeterssonHilbertCompletion = UniformSpace.Completion` (추상), 그러나 23846 `PhysicalLocalL2` 에서 `MeasureTheory.Lp ℂ 2` (carrier 위 Euclid 측도) 로의 **등거리 매장** 브리지 증명 (24171). 전사성(=C_c^∞ 의 L² 밀도)은 주장하지 않음 — 표준적 사실이므로 무해하나 "L²(Γ\ℍ) 와 동일" 은 매장 수준에서만 성립.
- **H¹ / 그래프 공간** (Definition 1): `WithLp 2` 3중곱 그래프 범위의 완비화. JointlyClosable 증명(27649)으로 실제 닫힌 연산자 그래프와 일치(27612). **충실**.
- **시험함수**: Mathlib `TestFunction` 𝓓(upperPlaneOpen, ℂ). **충실**.
- **unbounded 연산자**: Mathlib `LinearPMap`, `†`, `closure`, `IsFormalAdjoint`, `HasCore`. **충실**.
- **곡선적분/발산정리/변수변환**: Mathlib `curveIntegral`, `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`, `integral_image_eq_integral_abs_det_fderiv_smul`, `UpperHalfPlane.smulFDeriv`. **충실**.
- **퍼텐셜**: VΔ 는 충실. 그러나 논문의 "compact potential"(헤더 항목 5)은 **rank-one 커널 대리물**로 대체 — VΔ 곱셈 연산자의 콤팩트성과 연결하는 정리 **없음** (21327–21343 주석이 정직히 Rellich 부재를 명시).

---

## 6. 실질 수학 vs 스캐폴딩 (범위 내, 줄 기준 추정)

비자명한 실질 증명(위 표 1–15 및 그 보조정리; 국소 분포론, 이중 수반, Piola/Jacobian, Green 정리, Δ-퍼텐셜 해석, 서로소 shell, cutoff 분할 등): **코드의 약 55–60% (≈6,800–7,300줄)**.
필수적이나 일상적인 인프라(선형성·연속성·지지·가측성·rfl/simp API, 인덱스 transport): **코드의 약 25–30%**.
순수 스캐폴딩/자명(별칭, iff 재진술, degenerate cusp-tail, 장난감 Fredholm, refl isometry, `#print axioms` 384줄, `#synth`): **코드의 약 12–15%**.
전체 줄(주석·공백 포함) 기준: 실질 수학 ≈ 45%, 인프라 ≈ 22%, 스캐폴딩 ≈ 10%, 주석/공백 ≈ 22%.
→ 앞선 모듈들(Mock1_Advanced 등)과 대조적으로 **이 구간은 실질 수학 밀도가 높다**.

주요 실질 증명(분량 상위): `physicalJointFromSucc_isClosable_of_components` (25960, 100줄), `integral_rectangle_piola_divergence_eq_boundary` (29629), `fixedPhaseGreenScalarDensity_covariance` (17627), `quotientCoordinates_jointlyClosable_of_jointGraph` (27314), `physicalRaise_isClosable` (25633), `setIntegral_heightSq_divergence_modularClosedTile_eq_boundary` (29863), `submodule_adjoint_adjoint_eq_topologicalClosure` (25209), `divergence_selectedCosetPiola` (30485), `orbitEuclidean_eq_zero_of_ambient_test_pairings` (25125), `GammaTwoActualPolygonEdge.paired_paired` (31143).

---

## 7. 수학적 정확성 / 과대 표기

오류로 판단되는 진술은 **발견하지 못함**. 과대/오해 소지:
1. 19879–19883 `pageFourHOneEquivPageTwelveGraph`: docstring "unconditional linear isometry, not a certificate field" — 실제로는 `PaperPageFourHOne` 과 `PaperPageTwelveGraphSpace` 가 **같은 abbrev** 이므로 `refl`. 두 독립 정의의 동일시 정리가 아니라 명명 선택 (설계 의도는 19861–19868 주석에 정직히 적혀 있음).
2. 21860 `explicitUnshiftedFredholmData` "Hypothesis-free nontrivial-kernel Fredholm data on the actual … Petersson Hilbert space": 공간·벡터는 실제이나 연산자 `I − P` 는 Maass/Laplace 와 무관한 장난감. Fredholm 대안의 "실제 적용"으로 읽히면 과대.
3. 21327 "An unconditional compact separable test kernel": rank-one 의 콤팩트성은 자명. 논문의 compact potential 주장을 이것으로 대체했음을 요약 레벨에서 명확히 해야 함 (모듈 내 주석은 정직).
4. 22467–22469 `denseRange_l2Coordinate`: "not the graph completion's defining dense-range statement" — 사실이지만, 결국 코어 전사 + 자기 완비화 밀도라 거의 정의적. 비자명 부분은 22432 코어 동치(앞 구간 공변성 정리 기반).
5. 23200–23384 "exact exhaustion … zero graph error": 코어가 몫-콤팩트이므로 자명 (문서가 "collapses" 라고 정직히 인정).
6. 27863/27873/27897: 가설 `PhysicalGreenIdentityAt` 의 재진술 (T given hyp). 단 가설은 33398 에서 해소.

---

## 8. 코드 품질

- **조직**: "## 7. Axiom audit" (26152) 이후에 P2.4/P2.6/P3.x 블록이 연대기식으로 덧붙고 namespace 를 반복 재개. 63k줄 단일 파일 — 분할 필요.
- **중복**: bump/cutoff 구성 4벌(`upstairsCoreCutoff`, `upstairsCuspCutoff`, `upstairsPotentialShell`, `upstairsAllIndexCoreCutoff`) 각각이 `_projected_support`/`_hasCompactSupport` 증명을 거의 그대로 복제. `hyperbolicDensity`(23861) 와 `hyperbolicDensityNNReal`(28450) 중복 정의. `…_of_green` 와 무조건 버전 이중 API.
- **취약성**: `set_option backward.isDefEq.respectTransparency false` (28565 `in`, 28822–29410 구간 전체, 31554/31591/31606) — defeq 투명도 규칙 완화; `CurvedTileCoherentInstances` 의 local instance 로 ℝ/ℂ/ℝ×ℝ 모듈 구조 고정 → 인스턴스 다이아몬드 회피용. `InverseEtaFixedPhaseCore` 에 대한 local `Module`/`AddCommGroup` 인스턴스 재선언 4회 (19655, 22321, 27186, 27850). 범위 내 `maxHeartbeats` 상향 **없음**.
- **가독성**: 25575–25612 의 완전수식 이름(`Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.PhysicalLocalL2.…`) 과다. 반면 docstring 은 매우 상세하고 정직.
- **Mathlib PR 가치**: `FormalAdjointClosure.submodule_adjoint_adjoint_eq_topologicalClosure`/`adjoint_dense_domain`/`adjoint_adjoint_eq_closure` (LinearPMap 이중 수반 = 닫힘, Mathlib 에 없음 — 최우선 후보), `isEssentialGraphCoreFor_iff_hasSequentialGraphCore`, `denseRange_iff_surjective_energyCompletionIsometry`, `CompactCoreL2.toL2_injective`, 등각사상 Piola 발산 항등식, `sum_actualPolygonEdges_eq_zero_of_paired_neg` 의 일반형(involution 반대칭 합 = 0).

---

## 10. 범위 한정 잠정 점수 (1–10)

| 축 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 9 | sorry/axiom 없음, 컴파일 확인됨; `Classical.choose` 7회 모두 증명된 ∃ 에서만; respectTransparency 토글만 약간의 위험 |
| 조건부 인증의 정직성(비순환성) | 8 | 가설은 명시·정직 문서화, Stokes/Green 가설은 이후(33349–33404) 실제 해소; 감점: Green/역포함 가설이 결론과 동치인 형태, degenerate cusp-tail, refl·장난감 모델의 과대 docstring |
| 수학적 실질성 | 8 | 국소 분포론적 닫힘가능성, T††=closure, 곡선 타일 Green, Möbius Piola, Δ-퍼텐셜, 무한차원성 등 진짜 해석학; VΔ 콤팩트성은 미해결(rank-one 로 대체) |
| 정의 충실도 | 8 | Mathlib 객체 일관 사용, Petersson 완비화→`Lp` 등거리 브리지; "compact potential" 은 브리지 없는 대리물 |
| 코드 품질·유지보수성 | 5 | 문서·증명 가독성 양호하나 거대 단일 파일, 연대기식 패치 구조, 대량 중복, 인스턴스 우회, `#print axioms` 384줄 |
| 종합 | 8 | 이 구간은 모듈 전체에서 가장 실질적인 부분 중 하나; 남은 진짜 공백(퍼텐셜 콤팩트성, essential core)이 정직히 표시됨 |

---

## 커버리지 로그

- 15900–17099 read (Read, 2회 분할)
- 17100–17699 read
- 17700–18299 read
- 18300–19499 read
- 19500–20499 read
- 20500–21499 read
- 21500–22499 read
- 22500–23499 read
- 23500–24499 read
- 24500–25499 read
- 25500–26199 read
- 26160–26479 **skim**: `#print axioms` 318줄만 존재 확인 (grep 으로 비-print 라인 없음 확인)
- 26505–27404 read
- 27405–28299 read
- 28300–29199 read
- 29200–29999 read
- 30000–30749 read
- 30750–31619 read
- 범위 밖 참조(검증용 grep/부분 열람): 15020–15150 (`ExponentIndexedDifferentialCore`, `GreenIdentity`), 33340–33420 (`gammaTwoPairedPolygonFluxStokes`, `gammaTwoCompactFluxStokes`, `physicalGreenIdentity_unconditional`), `StrongCrossAdjointAt` 사용처 37503–63073 (grep 만).
