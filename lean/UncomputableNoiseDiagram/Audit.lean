/-
# Axiom audit

Built by `scripts/audit.sh` (its log is copied to `AXIOMS.txt`).
* The final targets are printed with `#print axioms` and audited with `#audit_axioms_strict`
  (closed in session 10: only `propext`, `Classical.choice`, `Quot.sound`).
* Every proved leaf is audited with `#audit_axioms_strict`: only `propext`, `Classical.choice` and
  `Quot.sound` are allowed, and `sorryAx` is an error.
* `#audit_prefix UND` checks every declaration of the project (including private and generated
  ones) and lists those depending on `sorryAx`.
-/
import UncomputableNoiseDiagram
import UncomputableNoiseDiagram.AuditCommand

set_option autoImplicit false

/-! ## Final targets (closed) -/

#print axioms UND.theorem_A
#audit_axioms_strict UND.theorem_A
#print axioms UND.corollary_9_4
#audit_axioms_strict UND.corollary_9_4
#print axioms UND.one_rule_undecidable
#audit_axioms_strict UND.one_rule_undecidable

/-! ## Proved leaves (strict) -/

-- Corollary 9.4 and the one-rule corollary from Theorem 9.3 (`Corollary.lean`)
#audit_axioms_strict UND.midP_pos
#audit_axioms_strict UND.midP_val
#audit_axioms_strict UND.computable_midP
#audit_axioms_strict UND.promiseUndecidable_of_noiseDiagram
#audit_axioms_strict UND.corollaryNineFour_of_theoremA
#audit_axioms_strict UND.oneRuleUndecidable_of_corollary

-- The intervals (17) (`Windows.lean`)
#audit_axioms_strict UND.Windows.ell_add_one
#audit_axioms_strict UND.Windows.ell_pos
#audit_axioms_strict UND.Windows.ell_succ
#audit_axioms_strict UND.Windows.ell_mono
#audit_axioms_strict UND.Windows.seven_le_ell
#audit_axioms_strict UND.Windows.primrec_ell
#audit_axioms_strict UND.Windows.computable_loP
#audit_axioms_strict UND.Windows.computable_hiP
#audit_axioms_strict UND.Windows.presents_lo
#audit_axioms_strict UND.Windows.presents_hi
#audit_axioms_strict UND.Windows.ell_gap
#audit_axioms_strict UND.Windows.hi_lt_lo
#audit_axioms_strict UND.Windows.isWindowFamily_windows

-- Geometry and exact constants (`Parameters/Geometry.lean`)
#audit_axioms_strict UND.Param.K_eq
#audit_axioms_strict UND.Param.q_eq
#audit_axioms_strict UND.Param.h_eq
#audit_axioms_strict UND.Param.q_lt_two_h
#audit_axioms_strict UND.Param.q_sub_h
#audit_axioms_strict UND.Param.two_h_sub_q
#audit_axioms_strict UND.Param.V_eq
#audit_axioms_strict UND.Param.lam_eq
#audit_axioms_strict UND.Param.M_eq
#audit_axioms_strict UND.Param.q_sub_h_add_one
#audit_axioms_strict UND.Param.psi_sum
#audit_axioms_strict UND.Param.gain_zero_good
#audit_axioms_strict UND.Param.gain_i_good
#audit_axioms_strict UND.Param.gain_zero_worst
#audit_axioms_strict UND.Param.gain_i_worst
#audit_axioms_strict UND.Param.rho_values
#audit_axioms_strict UND.Param.A0_eq
#audit_axioms_strict UND.Param.spancount
#audit_axioms_strict UND.Param.spancount'
#audit_axioms_strict UND.Param.Omega_eq
#audit_axioms_strict UND.Param.H0_eq
#audit_axioms_strict UND.Param.rare_edges
#audit_axioms_strict UND.Param.Delta_eq
#audit_axioms_strict UND.Param.roles_le
#audit_axioms_strict UND.Param.degree_le
#audit_axioms_strict UND.Param.rare_degree_lt
#audit_axioms_strict UND.Param.two_geom_le
#audit_axioms_strict UND.Param.four_le_Kmem_pow
#audit_axioms_strict UND.Param.parents_le

-- The search (25) for `B = 4^k` (`Parameters/Search.lean`)
#audit_axioms_strict UND.Param.Delta_pos
#audit_axioms_strict UND.Param.Kmem_pos
#audit_axioms_strict UND.Param.Khist_pos
#audit_axioms_strict UND.Param.cden_pos
#audit_axioms_strict UND.Param.floor_zB
#audit_axioms_strict UND.Param.floor_uB
#audit_axioms_strict UND.Param.floor_wB
#audit_axioms_strict UND.Param.two_zpow_neg
#audit_axioms_strict UND.Param.zB_eq
#audit_axioms_strict UND.Param.uB_eq
#audit_axioms_strict UND.Param.wB_eq
#audit_axioms_strict UND.Param.four_inv_le
#audit_axioms_strict UND.Param.eta_lt
#audit_axioms_strict UND.Param.three_inv_lt
#audit_axioms_strict UND.Param.w_52386
#audit_axioms_strict UND.Param.w_52385
#audit_axioms_strict UND.Param.z_52386
#audit_axioms_strict UND.Param.u_52386
#audit_axioms_strict UND.Param.B_52386
#audit_axioms_strict UND.Param.mem_target
#audit_axioms_strict UND.Param.hist_target
#audit_axioms_strict UND.Param.mem_target_lower
#audit_axioms_strict UND.Param.bsearch_52386
#audit_axioms_strict UND.Param.not_bsearch_of_lt
#audit_axioms_strict UND.Param.exists_bsearch
#audit_axioms_strict UND.Param.bsearch_kParam
#audit_axioms_strict UND.Param.kParam_eq

-- The black-type comparison and the cutoff lemma (`Chart/BlackType.lean`)
#audit_axioms_strict UND.Chart.black_child_ff
#audit_axioms_strict UND.Chart.black_child_tt
#audit_axioms_strict UND.Chart.black_child_tf
#audit_axioms_strict UND.Chart.black_child_ft
#audit_axioms_strict UND.Chart.chain_black
#audit_axioms_strict UND.Chart.black_rank_compare
#audit_axioms_strict UND.Chart.exists_rank
#audit_axioms_strict UND.Chart.cutoff_of_filter

-- The generic PCA layer (`PCA/Process.lean`, `PCA/Markov.lean`)
#audit_axioms_strict UND.CA.isProbabilityMeasure_uniformLaw
#audit_axioms_strict UND.CA.uniformLaw_singleton
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseSite
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseLaw
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseLaw₂
#audit_axioms_strict UND.CA.apply_congr
#audit_axioms_strict UND.CA.measurable_of_local
#audit_axioms_strict UND.CA.measurable_apply_apply
#audit_axioms_strict UND.CA.measurable_apply
#audit_axioms_strict UND.CA.measurable_run
#audit_axioms_strict UND.CA.isProbabilityMeasure_law
#audit_axioms_strict UND.CA.law_zero
#audit_axioms_strict UND.CA.law_apply_eq_lintegral
#audit_axioms_strict UND.CA.law_dirac
#audit_axioms_strict UND.CA.noiseLaw_flags_eq
#audit_axioms_strict UND.CA.run_succ
#audit_axioms_strict UND.CA.run_one
#audit_axioms_strict UND.CA.run_succ_shift
#audit_axioms_strict UND.CA.measurable_slice0
#audit_axioms_strict UND.CA.measurable_shiftN
#audit_axioms_strict UND.CA.measurable_splitN
#audit_axioms_strict UND.CA.measurable_update
#audit_axioms_strict UND.CA.splitIdx_injective
#audit_axioms_strict UND.CA.noiseLaw_map_splitN
#audit_axioms_strict UND.CA.noiseLaw_map_slice0
#audit_axioms_strict UND.CA.noiseSite_map_eq
#audit_axioms_strict UND.CA.law_dirac_one
#audit_axioms_strict UND.CA.law_succ'
#audit_axioms_strict UND.CA.law_succ
#audit_axioms_strict UND.CA.siteLaw_pos

-- P4-P7: cylinders, coupling, Feller, translation invariance, forgetting and memory
-- (`PCA/Cylinder.lean`, `PCA/Feller.lean`, `PCA/Translation.lean`, `PCA/ForgetErgodic.lean`)
#audit_axioms_strict UND.CA.continuous_restrictWindow
#audit_axioms_strict UND.CA.measurable_restrictWindow
#audit_axioms_strict UND.CA.measurableSet_cyl
#audit_axioms_strict UND.CA.integral_cylIndicator
#audit_axioms_strict UND.CA.not_ergodic_of_memoryFrom
#audit_axioms_strict UND.CA.abs_le_dtv
#audit_axioms_strict UND.CA.dtv_le_of
#audit_axioms_strict UND.CA.dtv_nonneg
#audit_axioms_strict UND.CA.dtv_comm
#audit_axioms_strict UND.CA.dtv_le_one
#audit_axioms_strict UND.CA.deltaO_nonneg
#audit_axioms_strict UND.CA.dtv_le_deltaO
#audit_axioms_strict UND.CA.deltaO_le_of
#audit_axioms_strict UND.CA.abs_toReal_sub_le_of_subset
#audit_axioms_strict UND.CA.law_dirac_cyl
#audit_axioms_strict UND.CA.dtv_law_dirac_le
#audit_axioms_strict UND.CA.deltaO_le_disagree
#audit_axioms_strict UND.CA.forgets_of_coupling
#audit_axioms_strict UND.CA.continuous_of_local
#audit_axioms_strict UND.CA.continuous_apply_apply
#audit_axioms_strict UND.CA.continuous_applyMap
#audit_axioms_strict UND.CA.continuous_run
#audit_axioms_strict UND.CA.integral_law_dirac
#audit_axioms_strict UND.CA.integral_law
#audit_axioms_strict UND.CA.continuous_Phi
#audit_axioms_strict UND.CA.integral_Phi_law
#audit_axioms_strict UND.CA.isProbabilityMeasure_cesaro
#audit_axioms_strict UND.CA.integral_cesaro
#audit_axioms_strict UND.CA.isStationary_of_cesaro_limit
#audit_axioms_strict UND.CA.exists_cesaro_limit
#audit_axioms_strict UND.CA.exists_stationary
#audit_axioms_strict UND.CA.exists_window_approx
#audit_axioms_strict UND.CA.integral_window
#audit_axioms_strict UND.CA.weakTendsto_of_cyl
#audit_axioms_strict UND.CA.weakTendsto_iff_cyl
#audit_axioms_strict UND.CA.weakTendsto_iff_dtv
#audit_axioms_strict UND.CA.measurable_shift
#audit_axioms_strict UND.CA.continuous_shift
#audit_axioms_strict UND.CA.apply_shift
#audit_axioms_strict UND.CA.measurable_shiftNoise
#audit_axioms_strict UND.CA.run_shift
#audit_axioms_strict UND.CA.noiseLaw_map_shiftNoise
#audit_axioms_strict UND.CA.law_map_shift
#audit_axioms_strict UND.CA.isTI_law
#audit_axioms_strict UND.CA.isTI_cesaro
#audit_axioms_strict UND.CA.isTI_of_weakTendsto
#audit_axioms_strict UND.CA.isTI_of_cesaro_limit
#audit_axioms_strict UND.CA.measurable_law_dirac_apply
#audit_axioms_strict UND.CA.law_toReal_eq_integral
#audit_axioms_strict UND.CA.abs_law_sub_zero_le
#audit_axioms_strict UND.CA.dtv_law_le
#audit_axioms_strict UND.CA.law_of_stationary
#audit_axioms_strict UND.CA.ergodic_of_forgets
#audit_axioms_strict UND.CA.two_stationary_of_memory
#audit_axioms_strict UND.CA.hasTwoTIStationaryLaws_of_memory
#audit_axioms_strict UND.CA.not_ergodic_of_two
#audit_axioms_strict UND.CA.noiseDiagram_clauses

-- Q3 and the interval clauses of Prop 9.2 (`Parameters/Threshold.lean`)
#audit_axioms_strict UND.Param.DeltaRareOf_pos
#audit_axioms_strict UND.Param.KrareOf_pos
#audit_axioms_strict UND.Param.Krare_pos
#audit_axioms_strict UND.Param.C_pos
#audit_axioms_strict UND.Param.C_eq_inv
#audit_axioms_strict UND.Param.epsStarOf_pos
#audit_axioms_strict UND.Param.epsStarOf_le_C
#audit_axioms_strict UND.Param.epsStarOf_le_mem
#audit_axioms_strict UND.Param.epsStarOf_le_hist
#audit_axioms_strict UND.Param.epsStarOf_le_rare
#audit_axioms_strict UND.Param.epsStar_pos
#audit_axioms_strict UND.Param.epsStar_le_C
#audit_axioms_strict UND.Param.epsStar_le_mem
#audit_axioms_strict UND.Param.epsStar_le_hist
#audit_axioms_strict UND.Param.Krare_eq
#audit_axioms_strict UND.Param.epsStar_le_rare
#audit_axioms_strict UND.Param.ell_cast
#audit_axioms_strict UND.Param.exists_n0_general
#audit_axioms_strict UND.Param.exists_n0Search
#audit_axioms_strict UND.Param.n0Search_n0Param
#audit_axioms_strict UND.Param.n0Param_ge
#audit_axioms_strict UND.Param.isWindowFamily_final
#audit_axioms_strict UND.Param.hi_lt_of_search
#audit_axioms_strict UND.Param.hiF_lt_epsStar
#audit_axioms_strict UND.Param.window_subset
#audit_axioms_strict UND.Param.le_C_div_100
#audit_axioms_strict UND.Param.a_ge
#audit_axioms_strict UND.Param.ruler_margins

-- C1: Lemma 5.1, grouped terminal estimate (`Contour/Grouped.lean`)
#audit_axioms_strict UND.Contour.GroupedSystem.not_NF_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.rk_induction
#audit_axioms_strict UND.Contour.GroupedSystem.eq_of_reach_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.reach_sup
#audit_axioms_strict UND.Contour.GroupedSystem.reach_un
#audit_axioms_strict UND.Contour.GroupedSystem.term_trans
#audit_axioms_strict UND.Contour.GroupedSystem.term_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.term_isTerm_iff
#audit_axioms_strict UND.Contour.GroupedSystem.term_of_sup
#audit_axioms_strict UND.Contour.GroupedSystem.term_sup_iff
#audit_axioms_strict UND.Contour.GroupedSystem.term_un_iff
#audit_axioms_strict UND.Contour.GroupedSystem.g_of_NF
#audit_axioms_strict UND.Contour.GroupedSystem.g_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.rk_g
#audit_axioms_strict UND.Contour.GroupedSystem.reach_g
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_NF
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.isTerm_of_not
#audit_axioms_strict UND.Contour.GroupedSystem.g_induction
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.reach_gEnd
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_term
#audit_axioms_strict UND.Contour.GroupedSystem.exists_term
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_psi
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_spec
#audit_axioms_strict UND.Contour.GroupedSystem.reach_mono
#audit_axioms_strict UND.Contour.GroupedSystem.reach_symm
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_reach
#audit_axioms_strict UND.Contour.GroupedSystem.pEnd_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.pGrp_term
#audit_axioms_strict UND.Contour.GroupedSystem.pGrp_term_root
#audit_axioms_strict UND.Contour.GroupedSystem.pole_psi
#audit_axioms_strict UND.Contour.GroupedSystem.rel_symm
#audit_axioms_strict UND.Contour.GroupedSystem.rel_of_term
#audit_axioms_strict UND.Contour.GroupedSystem.mem_frontB_true
#audit_axioms_strict UND.Contour.GroupedSystem.mem_frontB_false
#audit_axioms_strict UND.Contour.GroupedSystem.rel_frontB_mono
#audit_axioms_strict UND.Contour.GroupedSystem.rel_split
#audit_axioms_strict UND.Contour.GroupedSystem.ov_frontU
#audit_axioms_strict UND.Contour.GroupedSystem.rel_frontU
#audit_axioms_strict UND.Contour.GroupedSystem.stepB_exists
#audit_axioms_strict UND.Contour.GroupedSystem.sum_insert_le'
#audit_axioms_strict UND.Contour.GroupedSystem.meas_frontB_lt
#audit_axioms_strict UND.Contour.GroupedSystem.meas_frontU_lt
#audit_axioms_strict UND.Contour.GroupedSystem.frontB_reach
#audit_axioms_strict UND.Contour.GroupedSystem.frontU_reach
#audit_axioms_strict UND.Contour.GroupedSystem.exists_poles
#audit_axioms_strict UND.Contour.GroupedSystem.exists_bij
#audit_axioms_strict UND.Contour.GroupedSystem.grouped_terminal_estimate
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_reach
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.armEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_subset_witness
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdge_mem_witness
#audit_axioms_strict UND.Contour.GroupedSystem.witness_connected
#audit_axioms_strict UND.Contour.GroupedSystem.root_mem_witness
#audit_axioms_strict UND.Contour.GroupedSystem.two_le_card_of_bound
#audit_axioms_strict UND.Contour.GroupedSystem.hosc_singleton
#audit_axioms_strict UND.Contour.GroupedSystem.singleton_two_le
#audit_axioms_strict UND.Contour.GroupedSystem.time_le_of_edgeReach
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_crossing_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.armEdges_crossing_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.witness_reach
#audit_axioms_strict UND.Contour.GroupedSystem.time_le_of_reach
#audit_axioms_strict UND.Contour.GroupedSystem.witness_span
#audit_axioms_strict UND.Contour.GroupedSystem.polebound_of_int
#audit_axioms_strict UND.Contour.GroupedSystem.grouped_terminal_estimate_paper

-- P8, P9, F5: Lemma 8.5 (`PCA/Pullback.lean`, `PCA/Attraction.lean`)
#audit_axioms_strict UND.CA.continuous_update
#audit_axioms_strict UND.CA.flow_succ'
#audit_axioms_strict UND.CA.pullback_succ
#audit_axioms_strict UND.CA.pullback_mono
#audit_axioms_strict UND.CA.history_succ
#audit_axioms_strict UND.CA.history_zero
#audit_axioms_strict UND.CA.exists_complete_of_pullback
#audit_axioms_strict UND.CA.exists_complete
#audit_axioms_strict UND.CA.pullback_eventually_singleton_of_unique
#audit_axioms_strict UND.CA.pullbackEventuallySingleton_of_unique
#audit_axioms_strict UND.CA.run_congr_cone
#audit_axioms_strict UND.CA.measurableSet_disagree
#audit_axioms_strict UND.CA.measurable_tau
#audit_axioms_strict UND.CA.noiseLaw₂_map_tau
#audit_axioms_strict UND.CA.flow_eq_run
#audit_axioms_strict UND.CA.pullFail_eq_preimage
#audit_axioms_strict UND.CA.measurableSet_pullFail
#audit_axioms_strict UND.CA.noiseLaw₂_pullFail
#audit_axioms_strict UND.CA.pullFail_antitone
#audit_axioms_strict UND.CA.forgets_of_unique
#audit_axioms_strict UND.CA.ergodic_of_unique

-- Q5: the series bases of Prop 9.2 (`Parameters/Bases.lean`)
#audit_axioms_strict UND.Param.Kmem_sqrt_C
#audit_axioms_strict UND.Param.etaHat_pos
#audit_axioms_strict UND.Param.mem_eta_base
#audit_axioms_strict UND.Param.mem_eta_base_kParam
#audit_axioms_strict UND.Param.mem_gamma_lt
#audit_axioms_strict UND.Param.mem_series_lt
#audit_axioms_strict UND.Param.raw_base_lt
#audit_axioms_strict UND.Param.rpow_sixteenth_lt
#audit_axioms_strict UND.Param.rare_base_lt
#audit_axioms_strict UND.Param.rare_base_lt_epsStarOf

-- Q4, Lemma 9.1: literal encoding bounds and the hook to Lemma 5.1 (`Contour/Counting.lean`)
#audit_axioms_strict UND.Counting.finite_connected
#audit_axioms_strict UND.Counting.mem_connSets
#audit_axioms_strict UND.Counting.connSets_spec
#audit_axioms_strict UND.Counting.card_connSets_le
#audit_axioms_strict UND.Counting.vertsOf_spec
#audit_axioms_strict UND.Counting.card_enc_le
#audit_axioms_strict UND.Counting.enc_term
#audit_axioms_strict UND.Counting.card_encLe_le
#audit_axioms_strict UND.Counting.mem_encLe
#audit_axioms_strict UND.Counting.four_mul_pow_le
#audit_axioms_strict UND.Counting.card_encLe_Kmem
#audit_axioms_strict UND.Counting.four_le_Kmem_pow_of_le
#audit_axioms_strict UND.Counting.four_le_KrareOf_pow
#audit_axioms_strict UND.Counting.card_encLe_KrareOf
#audit_axioms_strict UND.Counting.measure_biUnion_le_card_mul
#audit_axioms_strict UND.Counting.measure_le_tsum_groups
#audit_axioms_strict UND.Counting.tsum_ofReal_pow_succ
#audit_axioms_strict UND.Counting.measure_le_ofReal_tsum
#audit_axioms_strict UND.Counting.connectedAt_image
#audit_axioms_strict UND.Counting.connectedAt_filter_not_diag
#audit_axioms_strict UND.Counting.card_image_filter_le
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_le_two_gBin
#audit_axioms_strict UND.Contour.GroupedSystem.pLen_le_two_pBin
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_le_three_gBin
#audit_axioms_strict UND.Contour.GroupedSystem.pLen_le_three_pBin
#audit_axioms_strict UND.Contour.GroupedSystem.witness_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.witness_isEncoding

-- R1, R2: chart letters, the checker F_R and its iterates (`Rule/Checker.lean`)
#audit_axioms_strict UND.Rule.card_Prov
#audit_axioms_strict UND.Rule.provOff_mem
#audit_axioms_strict UND.Rule.quorum_unique
#audit_axioms_strict UND.Rule.quorumPick_eq_some_iff
#audit_axioms_strict UND.Rule.quorumPick_eq_none_iff
#audit_axioms_strict UND.Rule.FR_eq_some_iff
#audit_axioms_strict UND.Rule.FR_eq_none_iff
#audit_axioms_strict UND.Rule.chk_chart
#audit_axioms_strict UND.Rule.FR_cloned
#audit_axioms_strict UND.Rule.chk_translate
#audit_axioms_strict UND.Rule.quorumCount_translate
#audit_axioms_strict UND.Rule.FR_translate
#audit_axioms_strict UND.Rule.FR_iter_translate
#audit_axioms_strict UND.Rule.chk_congr
#audit_axioms_strict UND.Rule.FR_local
#audit_axioms_strict UND.Rule.mem_box_add
#audit_axioms_strict UND.Rule.FR_iter_local

-- R3, R4: helper alphabet, drivers, fields, Pin, the proposal (6), locality (`Rule/Proposal.lean`)
#audit_axioms_strict UND.Rule.Helper.rep_repr
#audit_axioms_strict UND.Rule.Helper.card_rep
#audit_axioms_strict UND.Rule.drvA_translate
#audit_axioms_strict UND.Rule.drvQ_translate
#audit_axioms_strict UND.Rule.Jf_translate
#audit_axioms_strict UND.Rule.hcount_translate
#audit_axioms_strict UND.Rule.lcount_translate
#audit_axioms_strict UND.Rule.Pin_translate
#audit_axioms_strict UND.Rule.proposal_translate
#audit_axioms_strict UND.Rule.card_nbhdA_le
#audit_axioms_strict UND.Rule.card_box
#audit_axioms_strict UND.Rule.card_nbhdQ
#audit_axioms_strict UND.Rule.card_nbhdP_le
#audit_axioms_strict UND.Rule.drvA_congr
#audit_axioms_strict UND.Rule.mem_cubeQ
#audit_axioms_strict UND.Rule.drvQ_congr
#audit_axioms_strict UND.Rule.proposal_local

-- R5, Prop 2.1: the proposal as one cellular automaton on Z^6 (`Rule/CA.lean`)
#audit_axioms_strict UND.Rule.caOf_apply
#audit_axioms_strict UND.Rule.card_nbhd_caOf
#audit_axioms_strict UND.Rule.ruleCA_apply
#audit_axioms_strict UND.Rule.prop_2_1

-- Q7, the assembly hook of Theorem 9.3 (`Assembly.lean`)
#audit_axioms_strict UND.window_rate
#audit_axioms_strict UND.noiseDiagram_of_branches
#audit_axioms_strict UND.theoremA_of_branches

-- R6: the noisy automaton in the paper's coordinates (`Rule/Noise.lean`)
#audit_axioms_strict UND.Rule.update_decode
#audit_axioms_strict UND.Rule.uniformLaw_decode
#audit_axioms_strict UND.Rule.swapField_swapField
#audit_axioms_strict UND.Rule.card_field_fiber_eq
#audit_axioms_strict UND.Rule.card_field_fiber
#audit_axioms_strict UND.Rule.uniformLaw_field

-- S5 arithmetic, FD2: the lane phase on finite bottom rows (`Chart/LanePhase.lean`)
#audit_axioms_strict UND.Chart.lanePhase_succ
#audit_axioms_strict UND.Chart.four_pow_eq
#audit_axioms_strict UND.Chart.wsum_dvd_sub
#audit_axioms_strict UND.Chart.lanePhase_bot
#audit_axioms_strict UND.Chart.lanePhase_bot_eq_zero_iff

-- S1 wiring, S6: walls at a finite-rank coordinate in every phase; l_d (`Chart/Walls.lean`)
#audit_axioms_strict UND.Chart.walls_VW_of_rank
#audit_axioms_strict UND.Chart.walls_HW_of_rank
#audit_axioms_strict UND.Chart.frameHi_sub_frameLo

-- S6, S8 first step: origins, ends, gates; finite ranks <= 2d in a closed frame (`Chart/Origins.lean`)
#audit_axioms_strict UND.Chart.exists_prank_le_of_inFrame
#audit_axioms_strict UND.Chart.inFrame_of_isLeftEnd
#audit_axioms_strict UND.Chart.inFrame_of_isRightEnd
#audit_axioms_strict UND.Chart.le_of_end_inFrame
#audit_axioms_strict UND.Chart.bottom_corner_iff
#audit_axioms_strict UND.Chart.orig_iff
#audit_axioms_strict UND.Chart.end_iff
#audit_axioms_strict UND.Chart.end_gate

-- S3, S4: the decorated scaffold and Lemma 3.2 (`Chart/Decorated.lean`)
#audit_axioms_strict UND.Chart.DQuarter.matchE_iff
#audit_axioms_strict UND.Chart.DQuarter.matchN_iff
#audit_axioms_strict UND.Chart.DQuarter.toQ_matchE
#audit_axioms_strict UND.Chart.DQuarter.toQ_matchN
#audit_axioms_strict UND.Chart.DQuarter.H_eq_of_matchE
#audit_axioms_strict UND.Chart.DQuarter.V_eq_of_matchN
#audit_axioms_strict UND.Chart.isQTiling_toQ
#audit_axioms_strict UND.Chart.H_row_const
#audit_axioms_strict UND.Chart.V_col_const
#audit_axioms_strict UND.Chart.filter_of_black
#audit_axioms_strict UND.Chart.exists_prank
#audit_axioms_strict UND.Chart.cutoff_of_dtiling
#audit_axioms_strict UND.Chart.cutoff_exists

-- S5: the lane-phase decoder (D7 radius; `Chart/PhaseTable.lean`)
#audit_axioms_strict UND.Chart.exists_qphase_shift
#audit_axioms_strict UND.Chart.wordAt_shift
#audit_axioms_strict UND.Chart.phaseTable_wordAt
#audit_axioms_strict UND.Chart.phaseTable_wordAt_eq_lanePhase
#audit_axioms_strict UND.Chart.phaseTable_wordAt_eq_zero_iff
#audit_axioms_strict UND.Chart.phaseTable_wordAt_add_e1
#audit_axioms_strict UND.Chart.phaseTable_wordAt_add_e2

-- S7, M1, R5/Q7 instance: the routing alphabet R, the machine P, theCA (`Chart/Routing.lean`, `Machine/P.lean`, `Chart/TheCA.lean`)
#audit_axioms_strict UND.prop_2_1_theCAOf
#audit_axioms_strict UND.theoremA_of_theCA

-- S7-S8: legal R-charts (projections, central words, the controller's readings) (`Chart/RChart.lean`)
#audit_axioms_strict UND.Chart.IsRChart.tileE
#audit_axioms_strict UND.Chart.IsRChart.tileN
#audit_axioms_strict UND.Chart.IsRChart.matchE
#audit_axioms_strict UND.Chart.IsRChart.matchN
#audit_axioms_strict UND.Chart.IsRChart.isDTiling
#audit_axioms_strict UND.Chart.IsRChart.isQTiling
#audit_axioms_strict UND.Chart.IsRChart.mem_box_iff
#audit_axioms_strict UND.Chart.IsRChart.word_apply
#audit_axioms_strict UND.Chart.IsRChart.word_eq
#audit_axioms_strict UND.Chart.IsRChart.phase_eq
#audit_axioms_strict UND.Chart.IsRChart.phase_eq_zero_iff
#audit_axioms_strict UND.Chart.IsRChart.gate_iff

-- S8, Lemma 3.3: walls and orientation on free lines; free x free sites active (`Chart/Board.lean`)
#audit_axioms_strict UND.Chart.strip_orient
#audit_axioms_strict UND.Chart.endpoint_lt_of_interior
#audit_axioms_strict UND.Chart.inFrame_of_isFree
#audit_axioms_strict UND.Chart.board_row_walls
#audit_axioms_strict UND.Chart.board_col_walls
#audit_axioms_strict UND.Chart.board_row
#audit_axioms_strict UND.Chart.board_col
#audit_axioms_strict UND.Chart.board_active

-- S8, Lemma 3.3: the laminar argument (non-free lines carry one direction) (`Chart/BoardGaps.lean`)
#audit_axioms_strict UND.Chart.exists_gap
#audit_axioms_strict UND.Chart.laminar_gap
#audit_axioms_strict UND.Chart.map_BT_side_eq_some
#audit_axioms_strict UND.Chart.map_LR_side_eq_some
#audit_axioms_strict UND.Chart.toBT_injective
#audit_axioms_strict UND.Chart.toLR_injective
#audit_axioms_strict UND.Chart.board_not_vcarrier
#audit_axioms_strict UND.Chart.board_not_hcarrier

-- S8, Lemma 3.3: the exact boundary flags (`Chart/BoardFlags.lean`)
#audit_axioms_strict UND.Chart.flag_first
#audit_axioms_strict UND.Chart.flag_second
#audit_axioms_strict UND.Chart.fW_of_map
#audit_axioms_strict UND.Chart.fE_of_map
#audit_axioms_strict UND.Chart.fS_of_map
#audit_axioms_strict UND.Chart.fN_of_map
#audit_axioms_strict UND.Chart.decide_ite_wall
#audit_axioms_strict UND.Chart.one_lt_ell_frame
#audit_axioms_strict UND.Chart.board_flags_row
#audit_axioms_strict UND.Chart.board_flags_col

-- S8, Lemma 3.3: channels, records and the board recursion (`Chart/BoardTableau.lean`)
#audit_axioms_strict UND.Chart.channel
#audit_axioms_strict UND.Chart.board_hchannel
#audit_axioms_strict UND.Chart.board_vchannel
#audit_axioms_strict UND.Chart.board_record
#audit_axioms_strict UND.Chart.board_tab
#audit_axioms_strict UND.Chart.board_init
#audit_axioms_strict UND.Chart.board_step
#audit_axioms_strict UND.Chart.board_vlink
#audit_axioms_strict UND.Chart.board_bottom
#audit_axioms_strict UND.Chart.board_top

-- M4, Lemma 4.2: which input is read (`Chart/Input.lean`)
#audit_axioms_strict UND.Chart.prank_of_half
#audit_axioms_strict UND.Chart.rfree_sub
#audit_axioms_strict UND.Chart.two_pow_succ_le
#audit_axioms_strict UND.Chart.four_pow_eq_two_pow_mul
#audit_axioms_strict UND.Chart.add_two_le_of_two_pow
#audit_axioms_strict UND.Chart.four_pow_split
#audit_axioms_strict UND.Chart.prank_left
#audit_axioms_strict UND.Chart.prank_center
#audit_axioms_strict UND.Chart.prank_right
#audit_axioms_strict UND.Chart.mod_of_odd_block
#audit_axioms_strict UND.Chart.not_isFree_of_mod
#audit_axioms_strict UND.Chart.free_left_rank
#audit_axioms_strict UND.Chart.free_right_rank
#audit_axioms_strict UND.Chart.exists_two_pow_mul_odd
#audit_axioms_strict UND.Chart.lt_of_isFree
#audit_axioms_strict UND.Chart.free_rank_even
#audit_axioms_strict UND.Chart.allowed_lift
#audit_axioms_strict UND.Chart.allowed_four_pow
#audit_axioms_strict UND.Chart.initial_zero
#audit_axioms_strict UND.Chart.count_initial_zero
#audit_axioms_strict UND.Chart.chi2_eq
#audit_axioms_strict UND.Chart.cutoff_of_flags
#audit_axioms_strict UND.Chart.input_read_large
#audit_axioms_strict UND.Chart.input_read_small

-- M2, Lemma 4.1(a): f_P is the sequential machine P (`Machine/Run.lean`)
#audit_axioms_strict UND.MachineP.nextRow_up
#audit_axioms_strict UND.MachineP.nextRow_stay
#audit_axioms_strict UND.MachineP.nextRow_down
#audit_axioms_strict UND.MachineP.nextRow_up_fail
#audit_axioms_strict UND.MachineP.nextRow_down_fail
#audit_axioms_strict UND.MachineP.colOf_eq
#audit_axioms_strict UND.MachineP.update_restrict
#audit_axioms_strict UND.MachineP.nextRow_colOf
#audit_axioms_strict UND.MachineP.nextRow_iterate
#audit_axioms_strict UND.MachineP.runP_eq
#audit_axioms_strict UND.MachineP.deltaP_fail
#audit_axioms_strict UND.MachineP.deltaP_halt
#audit_axioms_strict UND.MachineP.stepU_fail
#audit_axioms_strict UND.MachineP.stepU_iterate_fail
#audit_axioms_strict UND.MachineP.stepB_fail
#audit_axioms_strict UND.MachineP.stepU_halt
#audit_axioms_strict UND.MachineP.stepB_iterate
#audit_axioms_strict UND.MachineP.stepB_iterate_eq

-- M3, Lemma 4.1(b): steps, SCAN, the parity guard, RUN simulates U (`Machine/Scan.lean`)
#audit_axioms_strict UND.MachineP.stepU_up
#audit_axioms_strict UND.MachineP.stepU_stay
#audit_axioms_strict UND.MachineP.stepU_down
#audit_axioms_strict UND.MachineP.stepU_down_zero
#audit_axioms_strict UND.MachineP.head_stepU_le
#audit_axioms_strict UND.MachineP.head_iterate_le
#audit_axioms_strict UND.MachineP.Reaches.refl
#audit_axioms_strict UND.MachineP.Reaches.trans
#audit_axioms_strict UND.MachineP.Reaches.of_iterate
#audit_axioms_strict UND.MachineP.Reaches.step
#audit_axioms_strict UND.MachineP.move_up
#audit_axioms_strict UND.MachineP.move_down
#audit_axioms_strict UND.MachineP.scan_up
#audit_axioms_strict UND.MachineP.deltaP_ret_z
#audit_axioms_strict UND.MachineP.deltaP_ret
#audit_axioms_strict UND.MachineP.ret_home
#audit_axioms_strict UND.MachineP.stepU_state_halt
#audit_axioms_strict UND.MachineP.stepU_state_fail
#audit_axioms_strict UND.MachineP.iterate_halt
#audit_axioms_strict UND.MachineP.iterate_fail
#audit_axioms_strict UND.MachineP.not_halt_before
#audit_axioms_strict UND.MachineP.fail_after
#audit_axioms_strict UND.MachineP.never_halt_of_fail
#audit_axioms_strict UND.MachineP.program_forget
#audit_axioms_strict UND.MachineP.deltaP_forget
#audit_axioms_strict UND.MachineP.deltaP_ne_scan
#audit_axioms_strict UND.MachineP.stepU_ne_scan
#audit_axioms_strict UND.MachineP.update_forget
#audit_axioms_strict UND.MachineP.stepU_forget
#audit_axioms_strict UND.MachineP.iterate_forget
#audit_axioms_strict UND.MachineP.state_iterate_forget
#audit_axioms_strict UND.MachineP.deltaP_scan_one
#audit_axioms_strict UND.MachineP.deltaP_scan_plus
#audit_axioms_strict UND.MachineP.deltaP_scan_fail
#audit_axioms_strict UND.MachineP.scan_phase
#audit_axioms_strict UND.MachineP.scan_plus
#audit_axioms_strict UND.MachineP.scan_guard
#audit_axioms_strict UND.MachineP.scan_forever
#audit_axioms_strict UND.MachineP.wt_z
#audit_axioms_strict UND.MachineP.update_wt_u
#audit_axioms_strict UND.MachineP.deltaP_run
#audit_axioms_strict UND.MachineP.sim_step
#audit_axioms_strict UND.MachineP.sim_step_none
#audit_axioms_strict UND.MachineP.run_succ
#audit_axioms_strict UND.MachineP.sim_inv
#audit_axioms_strict UND.MachineP.sim_halts
#audit_axioms_strict UND.MachineP.sim_no_halt

-- M3, Lemma 4.1(b): halving passes, SKIP, FINDN/APPENDU (`Machine/Passes.lean`)
#audit_axioms_strict UND.MachineP.deltaP_plus
#audit_axioms_strict UND.MachineP.deltaP_setend
#audit_axioms_strict UND.MachineP.deltaP_r_skip
#audit_axioms_strict UND.MachineP.deltaP_r_mark
#audit_axioms_strict UND.MachineP.deltaP_r_even
#audit_axioms_strict UND.MachineP.deltaP_r_one
#audit_axioms_strict UND.MachineP.deltaP_appendN_one
#audit_axioms_strict UND.MachineP.deltaP_appendN_zero
#audit_axioms_strict UND.MachineP.deltaP_skip_lt
#audit_axioms_strict UND.MachineP.deltaP_skip_last
#audit_axioms_strict UND.MachineP.deltaP_findN_two
#audit_axioms_strict UND.MachineP.deltaP_findN_one
#audit_axioms_strict UND.MachineP.deltaP_findN_zero
#audit_axioms_strict UND.MachineP.deltaP_appendU_one
#audit_axioms_strict UND.MachineP.deltaP_appendU_zero
#audit_axioms_strict UND.MachineP.update_wt_p
#audit_axioms_strict UND.MachineP.update_wt_n
#audit_axioms_strict UND.MachineP.reach_up
#audit_axioms_strict UND.MachineP.ret_home_wt
#audit_axioms_strict UND.MachineP.forget_tape1
#audit_axioms_strict UND.MachineP.plus_phase
#audit_axioms_strict UND.MachineP.pass_block
#audit_axioms_strict UND.MachineP.not_dvd_between
#audit_axioms_strict UND.MachineP.passP_succ
#audit_axioms_strict UND.MachineP.pass_blocks
#audit_axioms_strict UND.MachineP.passP_end
#audit_axioms_strict UND.MachineP.two_pow_split
#audit_axioms_strict UND.MachineP.halving_step
#audit_axioms_strict UND.MachineP.halving_all
#audit_axioms_strict UND.MachineP.halving_last
#audit_axioms_strict UND.MachineP.skip_loop
#audit_axioms_strict UND.MachineP.skip_phase
#audit_axioms_strict UND.MachineP.update_wt_u'
#audit_axioms_strict UND.MachineP.zero_ne_one_sym
#audit_axioms_strict UND.MachineP.copy_step
#audit_axioms_strict UND.MachineP.copy_all
#audit_axioms_strict UND.MachineP.copy_last
#audit_axioms_strict UND.MachineP.fnTok_last
#audit_axioms_strict UND.MachineP.uTape_eq_start
#audit_axioms_strict UND.MachineP.reaches_run

-- M3, Lemma 4.1(b): decoding, halting, the guard, on the board (`Machine/Decode.lean`)
#audit_axioms_strict UND.MachineP.forgetC_tape1
#audit_axioms_strict UND.MachineP.forget_scan
#audit_axioms_strict UND.MachineP.decode_halts
#audit_axioms_strict UND.MachineP.decode_no_halt
#audit_axioms_strict UND.MachineP.guard_no_halt
#audit_axioms_strict UND.MachineP.runP_no_halt
#audit_axioms_strict UND.MachineP.runP_halts

-- S8, Lemma 3.3 indexed: the board carries the run of P (`Chart/BoardRun.lean`)
#audit_axioms_strict UND.Chart.freeOff_finite
#audit_axioms_strict UND.Chart.count_freeOff
#audit_axioms_strict UND.Chart.card_freeOff
#audit_axioms_strict UND.Chart.freeOff_nth
#audit_axioms_strict UND.Chart.freeAt_free
#audit_axioms_strict UND.Chart.freeOff_zero
#audit_axioms_strict UND.Chart.nth_freeOff_zero
#audit_axioms_strict UND.Chart.freeAt_zero
#audit_axioms_strict UND.Chart.freeAt_lt
#audit_axioms_strict UND.Chart.freeAt_eq_zero_iff
#audit_axioms_strict UND.Chart.freeAt_consec
#audit_axioms_strict UND.Chart.freeAt_last
#audit_axioms_strict UND.Chart.board_run

-- M6, Prop 4.3 halting branch: a wrong flag in every legal chart, every phase (`Chart/Halting.lean`)
#audit_axioms_strict UND.Chart.prank_frameLo
#audit_axioms_strict UND.Chart.isEnd_of_bottomEnd
#audit_axioms_strict UND.Chart.bottomEnd_gate
#audit_axioms_strict UND.Chart.chart_wrong_flag

-- M5 groundwork: the read-only tracks are never written (`Machine/Decode.lean`)
#audit_axioms_strict UND.MachineP.program_tracks
#audit_axioms_strict UND.MachineP.deltaP_tracks
#audit_axioms_strict UND.MachineP.update_tracks
#audit_axioms_strict UND.MachineP.stepB_tracks
#audit_axioms_strict UND.MachineP.runP_tracks

-- M5, Prop 4.3 nonhalting, first part: no board halts under the correct cutoff (`Chart/NonHalting.lean`)
#audit_axioms_strict UND.Chart.prankOf_spec
#audit_axioms_strict UND.Chart.prankOf_eq
#audit_axioms_strict UND.Chart.board_no_halt
#audit_axioms_strict UND.Chart.board_run_no_halt

-- M5, Prop 4.3 nonhalting: the computational chart of a typical phase (`Chart/Construct.lean`)
#audit_axioms_strict UND.Chart.nd_eq
#audit_axioms_strict UND.Chart.freeAt_eq_zeta
#audit_axioms_strict UND.Chart.rankOK_okBits
#audit_axioms_strict UND.Chart.dqOf_toQ
#audit_axioms_strict UND.Chart.exists_prank_of_notInt
#audit_axioms_strict UND.Chart.dqOf_spec
#audit_axioms_strict UND.Chart.HSegM.hseg
#audit_axioms_strict UND.Chart.VSegM.vseg
#audit_axioms_strict UND.Chart.GPosM.gpos
#audit_axioms_strict UND.Chart.HSegM_unique
#audit_axioms_strict UND.Chart.VSegM_unique
#audit_axioms_strict UND.Chart.GPosM_unique
#audit_axioms_strict UND.Chart.lEm_of
#audit_axioms_strict UND.Chart.lEm_none
#audit_axioms_strict UND.Chart.lNm_of
#audit_axioms_strict UND.Chart.lNm_none
#audit_axioms_strict UND.Chart.kFm_of
#audit_axioms_strict UND.Chart.kFm_none
#audit_axioms_strict UND.Chart.sAt_zero
#audit_axioms_strict UND.Chart.sAt_of
#audit_axioms_strict UND.Chart.runP_succ
#audit_axioms_strict UND.Chart.sAt_succ
#audit_axioms_strict UND.Chart.lEm_gsite
#audit_axioms_strict UND.Chart.lWm_gsite
#audit_axioms_strict UND.Chart.lNm_gsite
#audit_axioms_strict UND.Chart.lSm_gsite
#audit_axioms_strict UND.Chart.kFm_gsite
#audit_axioms_strict UND.Chart.raw_active
#audit_axioms_strict UND.Chart.raw_O1
#audit_axioms_strict UND.Chart.raw_O2
#audit_axioms_strict UND.Chart.raw_E1
#audit_axioms_strict UND.Chart.raw_E2
#audit_axioms_strict UND.Chart.raw_E3
#audit_axioms_strict UND.Chart.raw_K1
#audit_axioms_strict UND.Chart.raw_K2
#audit_axioms_strict UND.Chart.raw_H
#audit_axioms_strict UND.Chart.raw_B
#audit_axioms_strict UND.Chart.raw_rules
#audit_axioms_strict UND.Chart.raw_K3
#audit_axioms_strict UND.Chart.raw_allowed
#audit_axioms_strict UND.Chart.raw_tileOK
#audit_axioms_strict UND.Chart.raw_matchE
#audit_axioms_strict UND.Chart.raw_matchN
#audit_axioms_strict UND.Chart.raw_tileE
#audit_axioms_strict UND.Chart.raw_tileN
#audit_axioms_strict UND.Chart.chartOf_val
#audit_axioms_strict UND.Chart.chartOf_isRChart
#audit_axioms_strict UND.Chart.chartOf_quarters
#audit_axioms_strict UND.Chart.chartOf_phase
#audit_axioms_strict UND.Chart.chartOf_V
#audit_axioms_strict UND.Chart.chartOf_H
#audit_axioms_strict UND.Chart.chartOf_bottom_flag

-- M5, Prop 4.3 nonhalting: equivariance, measurability, the translation-invariant chart law; D31 (`Chart/ChartLaw.lean`)
#audit_axioms_strict UND.Chart.dig_shift
#audit_axioms_strict UND.Chart.prank_iff_dig
#audit_axioms_strict UND.Chart.prank_shift
#audit_axioms_strict UND.Chart.prankOf_congr
#audit_axioms_strict UND.Chart.prankOf_shift
#audit_axioms_strict UND.Chart.fshift_phase
#audit_axioms_strict UND.Chart.fq_spec
#audit_axioms_strict UND.Chart.frameLo_shift
#audit_axioms_strict UND.Chart.frameHi_shift
#audit_axioms_strict UND.Chart.inFrame_shift
#audit_axioms_strict UND.Chart.isFree_shift
#audit_axioms_strict UND.Chart.zeta_shift
#audit_axioms_strict UND.Chart.pshift_addDig
#audit_axioms_strict UND.Chart.PShift.fcol
#audit_axioms_strict UND.Chart.PShift.frow
#audit_axioms_strict UND.Chart.PShift.zeta1
#audit_axioms_strict UND.Chart.PShift.zeta2
#audit_axioms_strict UND.Chart.PShift.prank1
#audit_axioms_strict UND.Chart.PShift.prank2
#audit_axioms_strict UND.Chart.PShift.cutH_eq
#audit_axioms_strict UND.Chart.PShift.cutPi_eq
#audit_axioms_strict UND.Chart.runP_congr
#audit_axioms_strict UND.Chart.PShift.sAt_eq
#audit_axioms_strict UND.Chart.wdL_shift
#audit_axioms_strict UND.Chart.wdR_shift
#audit_axioms_strict UND.Chart.wtag_shift
#audit_axioms_strict UND.Chart.evTag_shift
#audit_axioms_strict UND.Chart.ptrans_addDig
#audit_axioms_strict UND.Chart.PTrans.rowW
#audit_axioms_strict UND.Chart.PTrans.colW
#audit_axioms_strict UND.Chart.PTrans.oEc
#audit_axioms_strict UND.Chart.PTrans.oNc
#audit_axioms_strict UND.Chart.PTrans.actF
#audit_axioms_strict UND.Chart.PTrans.eEc
#audit_axioms_strict UND.Chart.PTrans.eNc
#audit_axioms_strict UND.Chart.PTrans.dqOf
#audit_axioms_strict UND.Chart.PTrans.hseg
#audit_axioms_strict UND.Chart.PTrans.vseg
#audit_axioms_strict UND.Chart.PTrans.gsite
#audit_axioms_strict UND.Chart.PTrans.gpos
#audit_axioms_strict UND.Chart.PTrans.lEm
#audit_axioms_strict UND.Chart.PTrans.lNm
#audit_axioms_strict UND.Chart.PTrans.kFm
#audit_axioms_strict UND.Chart.PTrans.rawVal
#audit_axioms_strict UND.Chart.PTrans.wordAt
#audit_axioms_strict UND.Chart.PTrans.rawOf
#audit_axioms_strict UND.Chart.PTrans.chartOf
#audit_axioms_strict UND.Chart.chartOf_shift
#audit_axioms_strict UND.Chart.measurableSet_dig_col
#audit_axioms_strict UND.Chart.measurableSet_dig_row
#audit_axioms_strict UND.Chart.measurableSet_digP
#audit_axioms_strict UND.Chart.measurableSet_resolving
#audit_axioms_strict UND.Chart.measurableSet_typical
#audit_axioms_strict UND.Chart.haar_typical
#audit_axioms_strict UND.Chart.mlevel_pi
#audit_axioms_strict UND.Chart.mlevel_choose'
#audit_axioms_strict UND.Chart.mlevel_prankOf_col
#audit_axioms_strict UND.Chart.mlevel_prankOf_row
#audit_axioms_strict UND.Chart.mlevel_dqOf
#audit_axioms_strict UND.Chart.freeAt_congr
#audit_axioms_strict UND.Chart.mlevel_freeAt_row
#audit_axioms_strict UND.Chart.mlevel_cutH
#audit_axioms_strict UND.Chart.mlevel_cutPi
#audit_axioms_strict UND.Chart.mlevel_sAt
#audit_axioms_strict UND.Chart.measurableSet_HSegM
#audit_axioms_strict UND.Chart.measurableSet_VSegM
#audit_axioms_strict UND.Chart.measurableSet_GPosM
#audit_axioms_strict UND.Chart.mlevel_lEm
#audit_axioms_strict UND.Chart.mlevel_lNm
#audit_axioms_strict UND.Chart.mlevel_kFm
#audit_axioms_strict UND.Chart.mlevel_rawVal
#audit_axioms_strict UND.Chart.mlevel_rawOf
#audit_axioms_strict UND.Chart.measurable_chartOf
#audit_axioms_strict UND.Chart.measurable_quartersOf
#audit_axioms_strict UND.Chart.isProbabilityMeasure_chartLaw
#audit_axioms_strict UND.Chart.chartLaw_shift
#audit_axioms_strict UND.Chart.measurableSet_goodChart
#audit_axioms_strict UND.Chart.goodChart_chartOf
#audit_axioms_strict UND.Chart.ae_goodChart
#audit_axioms_strict UND.Chart.chart_law_exists

-- C3, Lemma 5.3 (coherence of unmarked live letters) and the raw marked set (`Contour/Coherence.lean`)
#audit_axioms_strict UND.Coh.card_PSrc
#audit_axioms_strict UND.Coh.insertNth_inj
#audit_axioms_strict UND.Coh.pHi_injective
#audit_axioms_strict UND.Coh.pLo_injective
#audit_axioms_strict UND.Coh.provOff_pair
#audit_axioms_strict UND.Coh.exists_pair
#audit_axioms_strict UND.Coh.sep_zero
#audit_axioms_strict UND.Coh.sep_step
#audit_axioms_strict UND.Coh.UL.drvA
#audit_axioms_strict UND.Coh.one_cluster
#audit_axioms_strict UND.Coh.card_cluster
#audit_axioms_strict UND.Coh.card_marked_le
#audit_axioms_strict UND.Coh.card_failed_le
#audit_axioms_strict UND.Coh.ul_of_good
#audit_axioms_strict UND.Coh.coh_rel
#audit_axioms_strict UND.Coh.coherence_eq
#audit_axioms_strict UND.Coh.coherence_compat
#audit_axioms_strict UND.Coh.coh_back
#audit_axioms_strict UND.Coh.coh_persist
#audit_axioms_strict UND.Coh.step_toward
#audit_axioms_strict UND.Coh.coh_cover
#audit_axioms_strict UND.Coh.coherent_chart
#audit_axioms_strict UND.Coh.markedAt_mono
#audit_axioms_strict UND.Coh.twoCl_mono
#audit_axioms_strict UND.Coh.markedFrom_mono
#audit_axioms_strict UND.Coh.markedFrom_mono'
#audit_axioms_strict UND.Coh.marked_closed

-- C3, Lemma 5.3 for the complete trajectories of the automaton (`Contour/Coherence.lean`)
#audit_axioms_strict UND.Coh.isFlagTraj_of_complete
#audit_axioms_strict UND.Coh.coherence_complete

-- C2, Lemma 5.2 (raw paths): the marked derivation as a grouped support graph, contours, the path argument, the union bound (`Contour/RawPaths.lean`)
#audit_axioms_strict UND.Raw.chi_par
#audit_axioms_strict UND.Raw.par_time
#audit_axioms_strict UND.Raw.par_ne
#audit_axioms_strict UND.Raw.card_box_one
#audit_axioms_strict UND.Raw.card_nbr_le
#audit_axioms_strict UND.Raw.par_mem_nbr
#audit_axioms_strict UND.Raw.mem_nbr_par
#audit_axioms_strict UND.Raw.inGraph_par
#audit_axioms_strict UND.Raw.not_isDiag_par
#audit_axioms_strict UND.Raw.MF.time_lt
#audit_axioms_strict UND.Raw.mf_par
#audit_axioms_strict UND.Raw.exists_pgood
#audit_axioms_strict UND.Raw.pd_spec
#audit_axioms_strict UND.Raw.sel_box
#audit_axioms_strict UND.Raw.sel_mf
#audit_axioms_strict UND.Raw.sel_ne
#audit_axioms_strict UND.Raw.sys_sup
#audit_axioms_strict UND.Raw.sel_good
#audit_axioms_strict UND.Raw.isBlockOffset_prov
#audit_axioms_strict UND.Raw.psi_par
#audit_axioms_strict UND.Raw.isPotential_psi
#audit_axioms_strict UND.Raw.mf_of_reach
#audit_axioms_strict UND.Raw.flag_of_term
#audit_axioms_strict UND.Raw.gLen_eq_gBin
#audit_axioms_strict UND.Raw.armEdge_spec
#audit_axioms_strict UND.Raw.exists_edge_of_reach
#audit_axioms_strict UND.Raw.isContour_flag
#audit_axioms_strict UND.Raw.exists_contour_nf
#audit_axioms_strict UND.Raw.exists_contour
#audit_axioms_strict UND.Raw.card_pathEdges_le
#audit_axioms_strict UND.Raw.pathEdges_reach
#audit_axioms_strict UND.Raw.pathEdges_connected
#audit_axioms_strict UND.Raw.pathEdges_inGraph
#audit_axioms_strict UND.Raw.connectedAt_union
#audit_axioms_strict UND.Raw.inGraph_union
#audit_axioms_strict UND.Raw.exists_cover
#audit_axioms_strict UND.Raw.noiseLaw₂_flags_eq
#audit_axioms_strict UND.Raw.flags_measure
#audit_axioms_strict UND.Raw.measure_le_tsum_from
#audit_axioms_strict UND.Raw.pathEv_null
#audit_axioms_strict UND.Raw.raw_paths
#audit_axioms_strict UND.Raw.raw_paths_threshold

-- C4, Lemma 5.4 (deep wrong readings): virtual levels on the marked derivation, the deep contour, Lemma 5.4 and its lag form (`Contour/Deep.lean`)
#audit_axioms_strict UND.Deep.T_eq
#audit_axioms_strict UND.Deep.exists_two_clusters
#audit_axioms_strict UND.Deep.prop_of_mem_filter'
#audit_axioms_strict UND.Deep.chk_center
#audit_axioms_strict UND.Deep.Ctx.depth_spec
#audit_axioms_strict UND.Deep.Ctx.depth_le
#audit_axioms_strict UND.Deep.Ctx.exists_pgoodD_a
#audit_axioms_strict UND.Deep.Ctx.zero_mem_box
#audit_axioms_strict UND.Deep.Ctx.exists_pgoodD_v
#audit_axioms_strict UND.Deep.Ctx.pdD_spec
#audit_axioms_strict UND.Deep.Ctx.childOK_sel
#audit_axioms_strict UND.Deep.Ctx.selD_ne
#audit_axioms_strict UND.Deep.Ctx.rk_supD
#audit_axioms_strict UND.Deep.Ctx.sysD_sup
#audit_axioms_strict UND.Deep.Ctx.selD_good
#audit_axioms_strict UND.Deep.Ctx.isPotential_psiD
#audit_axioms_strict UND.Deep.Ctx.inv_reach
#audit_axioms_strict UND.Deep.Ctx.flag_of_termD
#audit_axioms_strict UND.Deep.Ctx.gBin_add_level
#audit_axioms_strict UND.Deep.Ctx.gLen_eq_gBinD
#audit_axioms_strict UND.Deep.Ctx.armEdge_specD
#audit_axioms_strict UND.Deep.card_nbrD_le
#audit_axioms_strict UND.Deep.inGraphD_step
#audit_axioms_strict UND.Deep.not_isDiag_step
#audit_axioms_strict UND.Deep.exists_deep_contour
#audit_axioms_strict UND.Deep.deep_wrong
#audit_axioms_strict UND.Deep.deep_wrong_lag

-- N3, Lemma 6.2 (intrinsic tails), the probabilistic core: Chernoff and Hoeffding for independent {0,1} variables, the numerics, the bases (`Sensors/Tails.lean`)
#audit_axioms_strict UND.Sensors.integrable_of_zero_one
#audit_axioms_strict UND.Sensors.mgf_le_of_zero_one
#audit_axioms_strict UND.Sensors.chernoff_zero_one
#audit_axioms_strict UND.Sensors.chernoff_ratio
#audit_axioms_strict UND.Sensors.log_75_53
#audit_axioms_strict UND.Sensors.log_four_gt
#audit_axioms_strict UND.Sensors.short_exponent
#audit_axioms_strict UND.Sensors.exp_neg_le_two_zpow
#audit_axioms_strict UND.Sensors.short_tail
#audit_axioms_strict UND.Sensors.hoeffding_zero_one
#audit_axioms_strict UND.Sensors.long_tail
#audit_axioms_strict UND.Sensors.geom_three_le
#audit_axioms_strict UND.Sensors.lower_law_gt
#audit_axioms_strict UND.Sensors.ell_cast
#audit_axioms_strict UND.Sensors.short_support_lt
#audit_axioms_strict UND.Sensors.uB_cast
#audit_axioms_strict UND.Sensors.zB_cast
#audit_axioms_strict UND.Sensors.wB_cast
#audit_axioms_strict UND.Sensors.eta_bound
#audit_axioms_strict UND.Sensors.etaHat_cast

-- N1, the ideal experiments and the laws (14), (15); independence of disjoint coordinate sets (`Sensors/Ideal.lean`)
#audit_axioms_strict UND.Sensors.measurable_extend
#audit_axioms_strict UND.Sensors.extend_restrict
#audit_axioms_strict UND.Sensors.preimage_of_detBy
#audit_axioms_strict UND.Sensors.infinitePi_inter_eq_mul
#audit_axioms_strict UND.Sensors.measurableSet_coord
#audit_axioms_strict UND.Sensors.set_mark
#audit_axioms_strict UND.Sensors.set_noflag
#audit_axioms_strict UND.Sensors.measurableSet_rideEv
#audit_axioms_strict UND.Sensors.detBy_rideEv
#audit_axioms_strict UND.Sensors.infinitePi_coord
#audit_axioms_strict UND.Sensors.rideEv_real
#audit_axioms_strict UND.Sensors.uniformLaw_fieldSet
#audit_axioms_strict UND.Sensors.uniformLaw_upMark
#audit_axioms_strict UND.Sensors.uniformLaw_loMark
#audit_axioms_strict UND.Sensors.upper_law
#audit_axioms_strict UND.Sensors.lower_law

-- N2, Lemma 6.1 (ownership): independence on disjoint coordinate sets, characteristics, rides, gates, ownership (`Sensors/Ownership.lean`)
#audit_axioms_strict UND.Sensors.detBy_mono
#audit_axioms_strict UND.Sensors.detBy_empty
#audit_axioms_strict UND.Sensors.detBy_biInter
#audit_axioms_strict UND.Sensors.detBy_biUnion
#audit_axioms_strict UND.Sensors.measurableSet_of_detBy
#audit_axioms_strict UND.Sensors.infinitePi_biInter_eq_prod
#audit_axioms_strict UND.Sensors.iIndepFun_of_detBy
#audit_axioms_strict UND.Sensors.laneAtom_inj
#audit_axioms_strict UND.Sensors.ride_length
#audit_axioms_strict UND.Sensors.ride_nodup
#audit_axioms_strict UND.Sensors.mem_ride
#audit_axioms_strict UND.Sensors.ride_disjoint
#audit_axioms_strict UND.Sensors.IsGate.lanePhase
#audit_axioms_strict UND.Sensors.isGate_of_end
#audit_axioms_strict UND.Sensors.phaseZero_block
#audit_axioms_strict UND.Sensors.depth_unique
#audit_axioms_strict UND.Sensors.rightEnd_dvd
#audit_axioms_strict UND.Sensors.rightEnd_eq
#audit_axioms_strict UND.Sensors.ell_lt_four_pow
#audit_axioms_strict UND.Sensors.ownership
#audit_axioms_strict UND.Sensors.mem_gateAtoms
#audit_axioms_strict UND.Sensors.gateAtoms_disjoint

-- N3 at one gate: short and long bad events, independent lanes, their tails (`Sensors/Gate.lean`)
#audit_axioms_strict UND.Sensors.laneCount_congr
#audit_axioms_strict UND.Sensors.detBy_shortBad
#audit_axioms_strict UND.Sensors.detBy_longBad
#audit_axioms_strict UND.Sensors.laneInd_zero_one
#audit_axioms_strict UND.Sensors.measurable_laneInd
#audit_axioms_strict UND.Sensors.sum_laneInd
#audit_axioms_strict UND.Sensors.lanes_iIndep
#audit_axioms_strict UND.Sensors.upper_mean_le
#audit_axioms_strict UND.Sensors.shortBad_le_of
#audit_axioms_strict UND.Sensors.longBad_le_of
#audit_axioms_strict UND.Sensors.pLaw_eq
#audit_axioms_strict UND.Sensors.isProbabilityMeasure_pLaw
#audit_axioms_strict UND.Sensors.isProbabilityMeasure_noiseSite
#audit_axioms_strict UND.Sensors.shortBad_le
#audit_axioms_strict UND.Sensors.longBad_le

-- N4, Lemma 6.3 (joint source bound) abstract and for the automaton; Lemma 6.2 per bin (`Sensors/Joint.lean`)
#audit_axioms_strict UND.Sensors.biInter_union_subset
#audit_axioms_strict UND.Sensors.exists_big_class
#audit_axioms_strict UND.Sensors.min_le_sqrt_mul
#audit_axioms_strict UND.Sensors.real_biInter_eq_prod
#audit_axioms_strict UND.Sensors.joint_bound
#audit_axioms_strict UND.Sensors.isRightEnd_iff
#audit_axioms_strict UND.Sensors.card_ends_le
#audit_axioms_strict UND.Sensors.rawList_nodup
#audit_axioms_strict UND.Sensors.rawList_length
#audit_axioms_strict UND.Sensors.rawSupp_disjoint
#audit_axioms_strict UND.Sensors.rawEv_le
#audit_axioms_strict UND.Sensors.ell_mono
#audit_axioms_strict UND.Sensors.Regime.ell_le
#audit_axioms_strict UND.Sensors.Regime.W_le_four
#audit_axioms_strict UND.Sensors.detBy_gateBad
#audit_axioms_strict UND.Sensors.gateAtoms_sub_statSupp
#audit_axioms_strict UND.Sensors.detBy_statEv
#audit_axioms_strict UND.Sensors.statSupp_disjoint
#audit_axioms_strict UND.Sensors.statEv_le
#audit_axioms_strict UND.Sensors.joint_source_bound

-- Section 6 at the selected parameters: the regime on every window, Lemma 6.3 with gammaOf (`Sensors/Selected.lean`)
#audit_axioms_strict UND.Sensors.Bparam_eq
#audit_axioms_strict UND.Sensors.cden_ge
#audit_axioms_strict UND.Sensors.C_le_hundredth
#audit_axioms_strict UND.Sensors.C_real_eq
#audit_axioms_strict UND.Sensors.regime_final
#audit_axioms_strict UND.Sensors.joint_source_final

-- Mem3, Lemma 7.2 (counting the memory witnesses), combinatorial core: linear group-link count, 167g/256g edge budget, encodings at every root, the union bound with Lemma 6.3 (`Memory/Count.lean`)
#audit_axioms_strict UND.Contour.GroupedSystem.prop_of_mem_filter
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdges_card_le_lin
#audit_axioms_strict UND.Contour.GroupedSystem.armEdge_step
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdge_spec
#audit_axioms_strict UND.Contour.GroupedSystem.mem_contour
#audit_axioms_strict UND.Contour.GroupedSystem.reach_image
#audit_axioms_strict UND.Contour.GroupedSystem.reach_filter_not_diag
#audit_axioms_strict UND.Contour.GroupedSystem.prepend
#audit_axioms_strict UND.Contour.GroupedSystem.mem_encoding_nonUN
#audit_axioms_strict UND.Contour.GroupedSystem.MemEnc.mono
#audit_axioms_strict UND.Contour.GroupedSystem.MemEnc.isEncoding
#audit_axioms_strict UND.Contour.GroupedSystem.mem_encoding
#audit_axioms_strict UND.Memory.mem_union

-- Mem2, the helper ride (Lemma 7.1, Lemma 8.1): actual intervals along a true ride with live drivers are the ideal experiment; h_w and l_w at a correct gate (`Memory/Ride.lean`)
#audit_axioms_strict UND.Memory.rep_field
#audit_axioms_strict UND.Memory.rideVal_append
#audit_axioms_strict UND.Memory.ride_succ
#audit_axioms_strict UND.Memory.rideEv_up_iff
#audit_axioms_strict UND.Memory.rideVal_of_rideEv_lo
#audit_axioms_strict UND.Memory.chSite_sub_jy
#audit_axioms_strict UND.Memory.chSite_pred
#audit_axioms_strict UND.Memory.chSite_add_jy
#audit_axioms_strict UND.Memory.laneAtom_eq
#audit_axioms_strict UND.Memory.copy_step
#audit_axioms_strict UND.Memory.origin_step
#audit_axioms_strict UND.Memory.ride_copy
#audit_axioms_strict UND.Memory.ride_short
#audit_axioms_strict UND.Memory.gate_J
#audit_axioms_strict UND.Memory.mem_filter'
#audit_axioms_strict UND.Memory.hcount_short
#audit_axioms_strict UND.Memory.lcount_long

-- Mem2/Mem3, Lemma 7.1 as a grouped derivation (bad values, two-cluster supports, characteristic links, the projected graph nbrM, terminal sources), Lemma 7.2 at every data error (`Memory/Derivation.lean`)
#audit_axioms_strict UND.Memory.one_le_T
#audit_axioms_strict UND.Memory.val_aV
#audit_axioms_strict UND.Memory.qV_planar
#audit_axioms_strict UND.Memory.val_qV
#audit_axioms_strict UND.Memory.rideBase_eq
#audit_axioms_strict UND.Memory.chSite_self
#audit_axioms_strict UND.Memory.chiOf_qV
#audit_axioms_strict UND.Memory.chiOf_rideBase
#audit_axioms_strict UND.Memory.chiOf_par
#audit_axioms_strict UND.Memory.psi_eq_chi
#audit_axioms_strict UND.Memory.supOf_aV
#audit_axioms_strict UND.Memory.MCtx.exists_pgood
#audit_axioms_strict UND.Memory.MCtx.exists_pgood_of_NF
#audit_axioms_strict UND.Memory.MCtx.pd_spec
#audit_axioms_strict UND.Memory.MCtx.sel_spec
#audit_axioms_strict UND.Memory.MCtx.sel_ne
#audit_axioms_strict UND.Memory.MCtx.unM_spec
#audit_axioms_strict UND.Memory.MCtx.rk_lt_of
#audit_axioms_strict UND.Memory.MCtx.rk_sup
#audit_axioms_strict UND.Memory.MCtx.rk_un
#audit_axioms_strict UND.Memory.MCtx.sel_good
#audit_axioms_strict UND.Memory.MCtx.isPotential_sysM
#audit_axioms_strict UND.Memory.MCtx.hgrp_sysM
#audit_axioms_strict UND.Memory.MCtx.hUUU_sysM
#audit_axioms_strict UND.Memory.ind_decide
#audit_axioms_strict UND.Memory.card_nbrM_le
#audit_axioms_strict UND.Memory.nbrM_le_Delta
#audit_axioms_strict UND.Memory.mem_nbrM_fwdS
#audit_axioms_strict UND.Memory.mem_nbrM_bwdS
#audit_axioms_strict UND.Memory.mem_nbrM_fwdU
#audit_axioms_strict UND.Memory.mem_nbrM_bwdU
#audit_axioms_strict UND.Memory.bin_cases
#audit_axioms_strict UND.Memory.bin_ind
#audit_axioms_strict UND.Memory.fM_eq_iff
#audit_axioms_strict UND.Memory.outT_supOf
#audit_axioms_strict UND.Memory.outT_zero
#audit_axioms_strict UND.Memory.outT_qV
#audit_axioms_strict UND.Memory.outT_aV
#audit_axioms_strict UND.Memory.MCtx.step_nbr
#audit_axioms_strict UND.Memory.MCtx.bad_of_reach
#audit_axioms_strict UND.Memory.mem_rideEv_true
#audit_axioms_strict UND.Memory.MCtx.bad_zero_iff
#audit_axioms_strict UND.Memory.MCtx.drvA_good
#audit_axioms_strict UND.Memory.MCtx.drvQ_good
#audit_axioms_strict UND.Memory.MCtx.chSite_ride_planar
#audit_axioms_strict UND.Memory.MCtx.term_source
#audit_axioms_strict UND.Memory.MCtx.mem_cover

-- Lemmas 7.1, 7.2, 6.3 together: the data error bound S < 1/4 (`Memory/Error.lean`)
#audit_axioms_strict UND.Memory.gamma_facts
#audit_axioms_strict UND.Memory.tsum_ofReal_mem
#audit_axioms_strict UND.Memory.joint_MP
#audit_axioms_strict UND.Memory.mem_bad_le

-- Mem1, the reference chart: the bit lift is a full legal chart; its gates (`Memory/RefChart.lean`)
#audit_axioms_strict UND.Memory.isLegalBlock_blockAt
#audit_axioms_strict UND.Memory.liftSym_eq
#audit_axioms_strict UND.Memory.ctr_liftChart
#audit_axioms_strict UND.Memory.liftChart_full
#audit_axioms_strict UND.Memory.leftEnd_back
#audit_axioms_strict UND.Memory.chart_gate

-- Mem1, the stationary helper initialization and the hybrid trajectory (D42) (`Memory/Init.lean`)
#audit_axioms_strict UND.Memory.firstHit_cons
#audit_axioms_strict UND.Memory.firstHit_map
#audit_axioms_strict UND.Memory.measurableSet_firstHit
#audit_axioms_strict UND.Memory.chainSite_zero
#audit_axioms_strict UND.Memory.chainSite_succ
#audit_axioms_strict UND.Memory.chainSite_add
#audit_axioms_strict UND.Memory.valX_succ
#audit_axioms_strict UND.Memory.initField_rec
#audit_axioms_strict UND.Memory.decode_encode
#audit_axioms_strict UND.Memory.encode_decode
#audit_axioms_strict UND.Memory.pastOf_zero
#audit_axioms_strict UND.Memory.X0_eq
#audit_axioms_strict UND.Memory.hyb_nonpos
#audit_axioms_strict UND.Memory.hyb_nat
#audit_axioms_strict UND.Memory.hyb_succ
#audit_axioms_strict UND.Memory.hyb_hyp

-- Mem1, the initial law: measurability, translation invariance, gluing of the noise, the law at time t (`Memory/InitLaw.lean`)
#audit_axioms_strict UND.Memory.measurable_X0
#audit_axioms_strict UND.Memory.X0_shift
#audit_axioms_strict UND.Memory.isProbabilityMeasure_initLaw
#audit_axioms_strict UND.Memory.initLaw_TI
#audit_axioms_strict UND.Memory.measurable_glue
#audit_axioms_strict UND.Memory.negPart_glue
#audit_axioms_strict UND.Memory.posPart_glue
#audit_axioms_strict UND.Memory.measurable_negPart
#audit_axioms_strict UND.Memory.measurable_posPart
#audit_axioms_strict UND.Memory.glue_law
#audit_axioms_strict UND.Memory.encode_hyb
#audit_axioms_strict UND.Memory.law_initLaw

-- Mem4, Theorem 7.3: the memory branch of Theorem 9.3 (`Memory/Theorem.lean`)
#audit_axioms_strict UND.Memory.Smem_nonneg
#audit_axioms_strict UND.Memory.Smem_lt
#audit_axioms_strict UND.Memory.law_initLaw_le
#audit_axioms_strict UND.Memory.one_le_n0
#audit_axioms_strict UND.Memory.nhalt_cutOf
#audit_axioms_strict UND.Memory.liftSym_eq_liftB
#audit_axioms_strict UND.Memory.measurableSet_cSf
#audit_axioms_strict UND.Memory.cSf_shift
#audit_axioms_strict UND.Memory.memLaw_prob
#audit_axioms_strict UND.Memory.memLaw_TI
#audit_axioms_strict UND.Memory.hyp_typical
#audit_axioms_strict UND.Memory.law_memLaw_le
#audit_axioms_strict UND.Memory.zero_mem_win0
#audit_axioms_strict UND.Memory.mem_cyl_liveOne
#audit_axioms_strict UND.Memory.memory_branch
#audit_axioms_strict UND.Memory.theorem_7_3
#audit_axioms_strict UND.Memory.theoremA_of_halting

-- F1, first step: complete trajectories satisfy HelperTraj and follow the proposal off flags (`Forget/Miss.lean`)
#audit_axioms_strict UND.Forget.helperTraj_of_complete
#audit_axioms_strict UND.Forget.data_of_complete

-- F1, Lemma 8.1: monotone rides and the missed-erasure implication (Forget/Miss.lean)
#audit_axioms_strict UND.Forget.isub_refl
#audit_axioms_strict UND.Forget.isub_both
#audit_axioms_strict UND.Forget.isub_withZero
#audit_axioms_strict UND.Forget.isub_zero_withZero
#audit_axioms_strict UND.Forget.hasOne_of_isub
#audit_axioms_strict UND.Forget.eq_one_of_isub
#audit_axioms_strict UND.Forget.mono_step
#audit_axioms_strict UND.Forget.mono_origin
#audit_axioms_strict UND.Forget.ride_mono
#audit_axioms_strict UND.Forget.ride_mono_short
#audit_axioms_strict UND.Forget.lcount_le_short
#audit_axioms_strict UND.Forget.lo_le_hcount
#audit_axioms_strict UND.Forget.missed_erasure

-- F1, the wrong critical gate of every full chart (Forget/Gate.lean)
#audit_axioms_strict UND.Forget.isRChart_ctr
#audit_axioms_strict UND.Forget.gate_facts
#audit_axioms_strict UND.Forget.halting_gate

-- F2, Lemma 8.2 probabilistic core: block witnesses, Hoelder, the union bound (Forget/History.lean)
#audit_axioms_strict UND.Forget.nxt_time
#audit_axioms_strict UND.Forget.flagSet_time
#audit_axioms_strict UND.Forget.card_flagSet
#audit_axioms_strict UND.Forget.wt_eq
#audit_axioms_strict UND.Forget.atomSet_time
#audit_axioms_strict UND.Forget.detBy_badSet
#audit_axioms_strict UND.Forget.measure_badSet_le
#audit_axioms_strict UND.Forget.le_mul_pow_three
#audit_axioms_strict UND.Forget.measure_WEv_le
#audit_axioms_strict UND.Forget.tsum_wt_le
#audit_axioms_strict UND.Forget.path_disp
#audit_axioms_strict UND.Forget.exists_witness
#audit_axioms_strict UND.Forget.card_boxP
#audit_axioms_strict UND.Forget.card_flagSets_le
#audit_axioms_strict UND.Forget.blkW_le
#audit_axioms_strict UND.Forget.blk_sum_le
#audit_axioms_strict UND.Forget.hpath_null

-- Q5, the history bases of Prop 9.2 (Forget/HistBase.lean)
#audit_axioms_strict UND.Forget.pow_four_le
#audit_axioms_strict UND.Forget.term_le
#audit_axioms_strict UND.Forget.sqrt_sqrt_facts
#audit_axioms_strict UND.Forget.hist_base

-- F2, Lemma 8.2 (Forget/Eliminate.lean)
#audit_axioms_strict UND.Forget.chSite_node
#audit_axioms_strict UND.Forget.detBy_badK
#audit_axioms_strict UND.Forget.atomsK_disjoint
#audit_axioms_strict UND.Forget.uld_back
#audit_axioms_strict UND.Forget.node_prop
#audit_axioms_strict UND.Forget.hpath_of_ul
#audit_axioms_strict UND.Forget.no_ul_generic

-- F3-F4, Lemma 8.4 via the raw set (Forget/Coupling.lean)
#audit_axioms_strict UND.Forget.proposal_of_dead
#audit_axioms_strict UND.Forget.live_marked
#audit_axioms_strict UND.Forget.disc_step
#audit_axioms_strict UND.Forget.flagged_complete
#audit_axioms_strict UND.Forget.card_nbC_le
#audit_axioms_strict UND.Forget.par_chi
#audit_axioms_strict UND.Forget.nbr_symm
#audit_axioms_strict UND.Forget.nbC_symm
#audit_axioms_strict UND.Forget.nbr_sub_nbC
#audit_axioms_strict UND.Forget.conEdge_card
#audit_axioms_strict UND.Forget.conEdge_reach
#audit_axioms_strict UND.Forget.conEdge_connected
#audit_axioms_strict UND.Forget.conEdge_inGraph
#audit_axioms_strict UND.Forget.pathEdges_inGraphC
#audit_axioms_strict UND.Forget.inGraph_unionC
#audit_axioms_strict UND.Forget.inGraph_nbr_C
#audit_axioms_strict UND.Forget.exists_cover_C
#audit_axioms_strict UND.Forget.degree_le_rare
#audit_axioms_strict UND.Forget.discEv_null
#audit_axioms_strict UND.Forget.coupling_generic

-- F4, Q5, the halting branch for the automaton (Forget/Halting.lean)
#audit_axioms_strict UND.Forget.gateOracle_theCA
#audit_axioms_strict UND.Forget.Khist_facts
#audit_axioms_strict UND.Forget.halting_branch_gen
#audit_axioms_strict UND.Forget.gate_bounds_final
#audit_axioms_strict UND.Forget.eta_final
#audit_axioms_strict UND.Forget.eps_hist_final
#audit_axioms_strict UND.Forget.rare_of
#audit_axioms_strict UND.Forget.rare_final
#audit_axioms_strict UND.Forget.halting_branch

/-! ## Every project declaration -/

#audit_prefix UND
