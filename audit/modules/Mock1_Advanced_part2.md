# Mock1_Advanced.lean — Part 2 범위 감사 (L7601–28400, 20,800줄)

감사 방법: `decls_cls.json`으로 범위 내 2,421개 선언 지도화(theorem 1,979 = accessor 1,055 + 비-accessor 924, def 306, structure 112, inductive 22, abbrev 2) → 모든 structure / reference 인스턴스 / 비-accessor 정리 중 비-포워딩 정리(약 125개)를 원문에서 직접 읽음. accessor `_at` 군과 포워딩 층은 python 분류 + 표본 판독으로 skim (구간은 커버리지 로그 참조). lake/lean 미실행, 저장소 미수정.

## 0. 범위 구조 요약
| 구간 | 내용 |
|---|---|
| 7601–8130 | `RequirementKey.Covered`(14개 키, 각 키 = checklist 필드들의 연언 재진술), `RequirementCoverageMatrix` L7798, `NamedRequirementCoverage` L7910, `UnconditionalCertificationBundle.coverage_matrix` L8043 (And.intro 재포장) |
| 8131–8405 | **reference 인스턴스**: `referenceFormalizationChecklist` L8183, `referenceCertificationBundle` L8285, `referenceCertificateRoute` L8376 |
| 8406–8941 | `AxiomAuditLayer.targets` L8424: 정리 이름 String 리스트 + 67개 `List.Mem "문자열"` 보조정리(L8552–8881) |
| 8942–11370 | `ObjectiveItem`, `ObjectiveAuditMatrix`, `ObjectiveDefinitionMatrix`, `RequestedDefinitionChecklist` L9767(345줄 Prop 재진술), `RequestedDefinitionItem.Covered` L10880(284줄 연언), `covered_by_checklist` |
| 11374–12495 | `IntegratedLayer.fileName`("Basic.lean","SPT.lean",…), `RequestedLayerBlueprint`, `LocalAuditCommand.shellText`, `EnvironmentPinManifest` L12114, `LakeProjectLockCertificate` L12300 |
| 12496–14768 | `IntegratedLayerAudit`, `RequestedDefinitionLayerMatrix`, `UnconditionalityPolicy` L12808, `AxiomAuditManifest` L12962, `AxiomAuditCompleteness` L13027 + reference forwarders |
| 14769–20008 | `CertificationReadiness` L14769, `EndToEndCertificationEvidence` L16103, `RequestedDefinitionFinalLedger` L17390, `RequestedDetailFinalLedger` L17714, `UnconditionalCertificationSeal` L18014, `CertificationHandoffSeal` L18219, `AdvancedFinalTheoremAggregation` L18451, `referenceEndToEndCertificationEvidence` L18703, reference 포워더 L18798–20008 |
| 20013–20050 | `Mock1Adv` 호환 namespace (entropy_intercept 등 포워딩) |
| 20052–22176 | `Mock1AdvancedCompatibilityCertificate` L20058, `UnconditionalCertificationReleaseEnvelope` L20247, `RequirementCompletionLedger` L20527(251줄), Paper 모듈 레지스트리/프로토콜/`AdvancedPaperInfrastructureLedger` |
| 22176–23075 | 논문층 소형 인증서들(PaperClaim, PrincipalPartSolve, SPTOverlap, MuKernelPaper, TailRatio, KStability, KernelSelection, PhaseMatch, BetaNormalization, CoefficientSeparation, PAdicMahlerFace, DegeneracyChannel, EntropyCardy, NamedConcreteInstance) |
| 23077–25140 | `Mock1Advanced` ns: 논문 절/정리/표/식 번호 enum, 라벨 레지스트리, Table 1(파라미터 11행)·잔차표(16행) 유리수 데이터, PaperTables 인증서 |
| 25140–26610 | Table 6 OLS 수치(α̂, β̂, γ̂, c_eff, RSS), Rademacher α 추출, tail dominance, Cardy 규약, Theorem I.8 `GrowthStabilityBaseChangeCertificate`, `Mock1EntropyCardyCertificate`, G-완료 인증서 |
| 26614–27195 | 주부분(principal part) 조립: T1/T2 블록, `MatVecRat`, 항등행렬 |
| 27196–27880 | 커널/커스프: `KernelSelectionRecord`, T/S 위상표, `KernelCuspCertificate` |
| 27889–28400 | β=1 Archimedean 정규화: `UnfoldingIdentityCertificate`, `BetaArchimedeanCertificate` |

## 2. 헤드라인 정리 (범위 내)
| 줄 | Lean 식별자 / 진술(요약) | 상태 |
|---|---|---|
| 8043 | `UnconditionalCertificationBundle.coverage_matrix (B) : RequirementCoverageMatrix B` — `B.requirement_audit` 필드들을 And.intro로 재포장 | T |
| 8297–8321 | `reference_requirement_audit`, `reference_coverage_matrix`, `reference_requirement_key_covered`, `reference_proof_field_discharge_matrix` — 퇴화 `referenceCertificationBundle`에 대한 위 정리 적용 | A/T |
| 12649 | `requested_definition_checklist (B) : RequestedDefinitionChecklist B` — `B.definitions.*` 필드 대입 | A |
| 18662 | `advanced_final_theorem_aggregation (E) : AdvancedFinalTheoremAggregation E` — 임의 E에 대해 E의 필드로부터 재조립 (def) | T |
| 20021 / 20029 | `Mock1Adv.entropy_intercept`, `Mock1Adv.entropy_beta_unique` — part 1의 `MockCert.entropy_intercept`/`entropy_beta_unique`로 포워딩 (원 증명은 진짜지만 쉬운 극한 유일성) | U(포워딩) |
| 20034 / 20042 | `corollary1_holomorphic`: `Fminus x = (I/2)*S*R x`, `S=0` ⇒ `Fminus x = 0`; `shadow_zero_of_S_zero`: `xiFhat = S*kappa*g`, `S=0` ⇒ 0 | T |
| 23421 | `theorem_and_diagnostic_labels_disjoint`, 23312 `AdvancedClaim.toNumberedLabel_injective` — enum 라벨 판별 | T(유한 판정) |
| 25225–25262 | `reference_alpha_hat_mem` … `reference_ceff_close_to_half` (\|ĉ_eff − 1/2\| ≤ 1/2500), `reference_rss_le_billionth` — 하드코딩 유리수에 대한 `norm_num` | U(산술만) |
| 25626 | `RationalTailDominanceCertificate.tail_le_threshold_main` — `tail ≤ ratio·main`, `ratio ≤ thr`, `main ≥ 0` ⇒ `tail ≤ thr·main` | U(자명 부등식) |
| 26961 / 26966 | `reference_t1_matvec_eq_rhs`([[1]]·[1]=[1]), `reference_t2_matvec_eq_rhs`(2×2 항등행렬) | U(자명) |
| 28156 | `BetaArchimedeanCertificate.final_coefficient_formula_at` — 필드 등식들의 calc 연쇄 | A |
| 21167 등 | `RequirementCompletionLedger.mock1_shadow_zero_at` 등 수백 개 `_at` | A |

범위 내에 모의 세타 함수, Appell–Lerch 합, Rademacher 급수, p-진 대상에 관한 **실질적 정리는 0개**.

## 4. 조건부 인증 감사
### 4.1 named hypothesis / certificate 분류
| 구조 (줄) | 분류 | 근거 |
|---|---|---|
| `RequirementCoverageMatrix` 7798, `NamedRequirementCoverage` 7910, `ObjectiveAuditMatrix` 9048, `ObjectiveDefinitionMatrix` 9093, `RequestedDefinitionChecklist` 9767, `RequestedDefinitionAuditMatrix` 11279, `IntegratedLayerAudit` 12496, `RequestedDefinitionLayerMatrix` 12543 | CIRCULAR(재진술) / DISCHARGED-trivially | 모든 필드가 `UnconditionalCertificationBundle`의 checklist 필드 재진술; 일반 `B`에 대해 L8043·12626–12790에서 필드 대입으로 "증명". 새 내용 없음 |
| `CertificationReadiness` 14769, `EndToEndCertificationEvidence` 16103, `RequestedDefinitionFinalLedger` 17390, `RequestedDetailFinalLedger` 17714, `UnconditionalCertificationSeal` 18014, `CertificationHandoffSeal` 18219, `AdvancedFinalTheoremAggregation` 18451, `UnconditionalCertificationReleaseEnvelope` 20247, `RequirementCompletionLedger` 20527, `AdvancedPaperInfrastructureLedger` 21894 | CIRCULAR(중첩 재포장) | 하위 인증서를 필드로 담고 같은 명제를 다시 필드로 요구; `requested_definition_final_ledger E` 등 def로 E로부터 즉시 생성 |
| `UnconditionalityPolicy` 12808 | CIRCULAR + 하드와이어 | 필드 타입이 퇴화 `referenceCertificationBundle` 고정 → "무조건성 정책"이 영(0) 데이터 번들에 대한 진술 |
| `AxiomAuditManifest` 12962 / `AxiomAuditCompleteness` 13027 | 명칭 과장 | `collectAxioms` 등 실제 공리 감사 없음; 정리 이름 String 리스트(`AxiomAuditLayer.targets`)와 커버리지 재진술 묶음 |
| `EnvironmentPinManifest` 12114, `LakeProjectLockCertificate` 12300 | 사실과 불일치(문자열 rfl) | `leanToolchainSpec = "leanprover/lean4:v4.31.0"`, `mathlibCommit = "fabf563a…"`를 필드로 "인증". 실제 저장소 `lean-toolchain` = `v4.33.0-rc1`, Mathlib = `8cbb95e6`. 참조 경로 `outputs/Mock1_Integrated.lean`, `MockCert/Audit.lean`, `scripts/audit.ps1`, `.github/workflows/lean.yml` 모두 저장소에 없음. 이 문자열들이 Seal/Envelope/Ledger에 반복 등장(예: 16156, 18505, 20280, 20733) |
| `IntegratedFileManifest` 11573 / `RequestedLayerBlueprint` 11710 / `PaperModuleRegistry` 21590 | 사실과 불일치 | "Basic.lean","SPT.lean","MuKernel.lean","PaperClaims.lean" 등 존재하지 않는 파일명을 rfl로 "인증" (실제는 단일 90k줄 파일) |
| **Prop + 증명 쌍 필드 9개**: `PrincipalPartSolveCertificate.shadowCancellation` 22531, `KStabilityCertificate.stableAtDouble` 22773, `FiniteMultiplierPhaseMatch.phaseCompatible` 22812, `DegeneracyChannelCertificate.useScalar` 22944, `PdfLabelAuditBoundary.citationParsingExternal` 23519, `RademacherAlphaExtractionCertificate.cEqualsOne` 25536, `UnfoldingIdentityCertificate.diagonalSelection` 27900, `BetaOneNormalizationCertificate.normalizationAccepted` 27927, `ArchimedeanIntegralCert.noResidualGammaTerm` 27991 | **SUSPECT-VACUOUS(설계상 공허)** | 명제 자체가 인스턴스가 고르는 필드 → reference는 전부 `:= True`, `True.intro` (L22563, 22796, 22833, 22976, 23546, 25584, 28197, 28225, 28240). 이후 `EntropyCardyGCompletionCertificate.rademacher_c_eq_one`(26320대) 같은 "요구조건"도 결국 `True` |
| `BetaNormalizationCertificate.normalized_eq` 22841 | T | `normalizedScalar = scalar + beta - beta` (항상 = scalar) |
| `GrowthStabilityBaseChangeCertificate` 25804 (논문 Theorem I.8) | SUSPECT/degenerate | reference(25881): `alphaByCusp := fun _ => referenceAlphaHat`(상수) → "기저변환 불변성"이 rfl; SPT M=1이라 `gcd(1,2)=1` "obstruction free"; `tailUpper := referenceRSSValue`(OLS 잔차제곱합을 Rademacher tail 상계로 사용) |
| `RationalTailDominanceCertificate` 25593 | degenerate | `mainLower := 1`(임의), `tailUpper := RSS` — tail/main 의 실제 해석과 무관 |
| `NormalizedCoefficientFormulaCertificate` 28020, `BetaArchimedeanCertificate` 28093 | degenerate | reference: mockCoeff ≡ thetaCoeff ≡ normalizedCoeff ≡ 1, Rademacher main ≡ 1, remainder 0, scalar/β 전부 1 |

### 4.2 reference 인스턴스 판정 — **전부 퇴화(degenerate), 실제 대상 0건**
- `referenceFormalizationChecklist` L8183: part 1의 퇴화 객체 그대로 조립 — `referenceAnalyticData`(μ=R=0), `referenceBruinierFunkeXi`(ξ=0), `referenceSlashGenerator`(S 자리에 T-transport), `referenceZeroQSeries`(0), `referenceTruncatedQSeries`(길이 0), `referenceLaurentQSeries`(0), `referenceCRTPortfolio`(모듈러 0개, `Fin.elim0`), 커스프 source=target=∞, 행렬 T. → `referenceCertificationBundle`(8285)이 이후 모든 Readiness/Seal/Envelope/Ledger reference의 뿌리.
- 논문층: `referencePrincipalPartSolve`(rows=order=0, shadowCancellation=True), `referenceTailRatioCertificate`(bound 0), `referenceKStabilityCertificate`(K=1, True), `referenceKernelSelectionCertificate`(modulus 1), `referenceCoefficientSeparation`(전부 0), `referenceMuKernelPaperCertificate`(shadow scale 0), `referenceDiagnosticTable`(α구간 [1,1], β구간 [0,0], 잔차 0).
- 주부분: `referenceT1PrincipalPart`/`T2`(order 1/2, **계수 전부 0**) vs `referenceT1ExponentInput.coefficient := 1` — 연결 필드 없음; 선형계 `zero*LinearSystemCertificate`는 열 0개; 조립 행렬은 항등행렬.
- 커널/커스프: level 1, multiplier ≡ 1, `slashAction := fun _ _ => 1`; `TSPhaseRow.computedValue := tableValue`(계산 없이 복사, 27599–27618), S-위상 √3/2 − i/2 는 상수로만 기입.
- 수치표: Table 1 11행·잔차표 16행·Table 6 값은 외부(Pydroid3 스크립트) 결과를 유리수로 옮겨 적은 것. Lean은 "값 ∈ singleton 구간", "값 ≤ 5", `pass := true` 정도만 검사 (예: `referenceParameterTableRow` 23704에서 `alphaInterval := singleton alpha`).
- **불일치**: `referenceMock1EntropyCardyCertificate`(26020)의 `concrete := referenceConcreteCertificate`는 α=1, β=0 (L3692–3693)인데 같은 인증서의 α̂ 구간은 [1.81437933628, 1.81439317540]. 두 α를 잇는 필드가 없어 "entropy/Cardy 인증"이 서로 다른 α를 동시에 담고 있음.

## 5. 정의 충실도
- 범위 내 새 수학 정의는 `RationalInterval`(22384, ad hoc 유리수 구간; Mathlib `Set.Icc` 미사용), `MatVecRat`/`dotRat`(26616–26621, List 기반 행렬곱; Mathlib `Matrix.mulVec` 미사용), `RationalRectangle`. 모의 세타/Appell–Lerch/Rademacher/p-진 대상의 정의는 없음(part 1의 임의함수 proxy를 재사용).
- "Theorem I.8", "Theorem K.2", "Theorem 1.1", "Theorem 3.2" 등은 `PaperTheoremNumber` enum과 String 라벨로만 존재. `AdvancedClaim.entropyGrowth ↦ Theorem 1.1`(23293)은 추상 함의(EntropyGrowth ⇒ intercept 극한)에 라벨을 붙인 것뿐, 특정 모의 세타 함수의 계수 점근을 진술하지 않음.
- 실제 개념과 proxy를 잇는 bridge 정리: 없음.

## 6. 실질 수학 vs scaffolding (범위 20,800줄)
| 분류 | 줄 | 비율 |
|---|---|---|
| accessor 정리 (`:= C.field`) | 6,478 | 31.1% |
| 비-accessor이지만 순수 포워딩 적용(`:= X.y_at …`, 799개) | ≈5,273 | 25.4% |
| 기타 비-accessor (cases/simp, List.Mem 사슬, And.intro 재포장, rfl) | ≈1,240 | 6.0% |
| structure 선언 (대부분 재진술 필드) | 2,911 | 14.0% |
| def (reference 인스턴스, String/enum 레지스트리, `Covered` 연언, 하드코딩 표) | 3,821 | 18.4% |
| inductive/abbrev/namespace·end/공백/주석 | ≈1,080 | 5.2% |
| **비자명 증명** (norm_num 유리수 검사 ≈45줄, `tail_le_threshold_main` 10줄, matvec 10줄, 리스트 보조정리 몇 개) | ≈70–100 | **≈0.3–0.5%** |
- 모의 세타·Appell–Lerch·Rademacher·p-진 수학에 관한 진짜 증명: **0%**. scaffolding ≈ 99.5%.

## 7. 수학적 정확성 / 과장 표현
1. 명칭 과장: `UnconditionalCertificationBundle`, `UnconditionalityPolicy`, `UnconditionalCertificationSeal`, `UnconditionalCertificationReleaseEnvelope`, `AxiomAuditCompleteness`, `EndToEndCertificationEvidence` — 전부 필드 재포장이며 공리 감사·end-to-end 검증을 하지 않음. 실제 내용은 퇴화 번들.
2. 환경 핀이 사실과 다름(4.1 참조): v4.31.0 / fabf563a vs 실제 v4.33.0-rc1 / 8cbb95e6; 존재하지 않는 파일·스크립트 경로를 "인증".
3. 25141–25147 docstring: "Rademacher asymptotics, tail estimates … carried as proof fields. The concrete instance fills the numerical part with rational intervals extracted from … Table 6 and Theorem I.8" — 실제 proof field는 `cEqualsOne := True` 등이며 tail 상계에 RSS를 사용. 표 수치는 외부 계산 결과의 전사일 뿐 Lean 안에서 재계산되지 않음.
4. `GrowthStabilityBaseChangeCertificate`(Theorem I.8 "기저변환 하 성장상수 안정성")는 reference에서 cusp별 α를 상수함수로 둬서 공허하게 만족.
5. (참고 관찰) c_eff = (6/π²)(α/2)² = 1/2 ⇔ α = π/√3 ≈ 1.8137994. 인증된 α̂ 구간 [1.8143793, 1.8143932]은 이 값을 **포함하지 않음**(차이 ≈5.9·10⁻⁴ ≈ 표준오차의 85배). `reference_ceff_close_to_half`는 허용오차 1/2500으로만 검사하므로 이 긴장 관계가 드러나지 않음. 논문이 정확히 α=π/√3를 주장하는지는 확인하지 못함.
6. `referenceSlashGenerator`(part 1)의 S=T 오류가 여기서 `RequirementKey.slash_transport` "covered"(7605–7616, 8062)로 그대로 인증됨.

## 8. 코드 품질
- 같은 명제가 ≥8개 층(Checklist → Coverage → Objective → RequestedDefinition → Readiness → EndToEnd → FinalLedger → Seal → Handoff → Aggregation → Envelope → CompletionLedger)에 재진술되고 층마다 `_at` accessor와 `reference_*` 포워더가 붙음 → 20.8k줄 중 실질 0.5% 미만. 유지보수성 매우 낮음(필드 하나 바꾸면 수십 곳 수정).
- `List.Mem.tail _ (List.Mem.tail _ …)` 손 사슬(7772–7785, 8552–8881 등 수백 줄) — `simp`/`decide`로 1줄 대체 가능.
- 문자열 상수(툴체인, 커밋, 경로)를 Prop 필드로 반복 고정 — 빌드 환경 변경 시 즉시 거짓이 되지만 rfl로 계속 "증명"됨.
- Mathlib upstream 가치: 없음.
- 범위 내 `set_option`/`sorry`/`axiom`/`native_decide` 없음(stripped copy grep 확인).

## 10. 범위별 잠정 점수 (1–10)
| 축 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 7 | 탈출구 없음·컴파일 확인(lead). 다만 Prop+증명 쌍 필드 9개가 공허 인스턴스를 허용 |
| 조건부 인증의 정직성(비순환성) | 2 | 층 전체가 재진술 순환, "Unconditional"/"AxiomAudit" 명칭 과장, 사실과 다른 환경 핀 |
| 수학적 실질성 | 1 | 대상 수학 정리 0개; 유리수 norm_num 몇 개뿐 |
| 정의 충실도 | 2 | 실제 대상 정의 없음, 수치표 전사, proxy–실제 bridge 없음 |
| 코드 품질·유지보수성 | 2 | 20.8k줄 중 ≈99.5% 보일러플레이트, 손 List.Mem 사슬 |
| 종합 | 2 | 인증 형식은 갖췄지만 내용은 퇴화 데이터와 재포장 |

## 커버리지 로그
- 원문 직독: 7601–8130, 8131–8558, 8880–9105, 9755–9900, 10100–10125, 10660–10700, 10780–10800, 10876–10900, 11150–11200, 11270–11420, 11573–11640, 11700–11790, 11924–11977, 12027–12040, 12114–12170, 12255–12356, 12496–12570, 12620–12660, 12745–12850, 12962–13070, 13987–14022, 14769–14812, 16103–16168, 18014–18030, 18451–18522, 20009–20210, 20247–20306, 20527–20560, 20700–20780, 21447–21475, 21590–21600, 21711–21832, 21894–21915, 22176–23076(전체, 빈줄 제외), 23077–23330, 23443–23460, 23514–23530, 23588–23740, 23831–23975, 24088–24175, 24236–24252, 24404–24416, 24559–24580, 24887–24900, 25140–25176, 25268–25410, 25528–25760, 25781–26045, 26085–26100, 26226–26363, 26614–26800, 26845–26870, 26971–27060, 27196–27380, 27583–27745, 27889–28130, 28191–28320, 28400–28405.
- python/decls_cls.json 분류 + 표본 판독으로 skim(전 선언 시그니처·본문 요약 확인): accessor 군 7944–8038, 9103–9764, 10114–10794, 11785–11888, 12372–12462, 13287–13984, 14815–15386, 17487–17661, 17809–17963, 18076–18182, 18286–18403, 18535–18659, 20784–21166, 21984–22083, 24618–24739, 26366–26465; 포워딩 정리 군 8558–8881(List.Mem 문자열), 14029–14768, 15591–16102, 16300–16622, 16679–17341, 18798–20008, 24327–24403, 27745–27876, 28320–28400; reference 레지스트리/ledger def 21177–21399, 22096–22153, 24742–25054.
- 범위 내 비-accessor 정리 924개 전부를 본문 패턴으로 분류(포워딩 799, rw/simp/exact 48, cases-simp 29, 구조 조립 8, List.Mem 12, 기타 28 — 기타 28개는 전부 원문 확인).
