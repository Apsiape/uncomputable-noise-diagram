/-
# Complete axiom audit (release package, Lean v4.35.0, Mathlib 56a0058)

Prints and strictly audits every root of `UncomputableNoiseDiagram/Audit.lean` (the three final
theorems first), then checks the axioms of every imported declaration of the development and of the
imported modules of the two reused cores (`FixedNoiseErgodicity.*`, `UndecidablePhaseDiagram.*`),
including private and generated ones: only `propext`, `Classical.choice`, `Quot.sound` are allowed,
and no such declaration is an axiom. Finally it checks the types of the three final theorems.
(Modelled on the hard-model and forgetting relays' package `Audit.lean`.)
-/
import UncomputableNoiseDiagram
import UncomputableNoiseDiagram.AuditCommand

set_option autoImplicit false

#print axioms UND.theorem_A
#audit_axioms_strict UND.theorem_A
#print axioms UND.corollary_9_4
#audit_axioms_strict UND.corollary_9_4
#print axioms UND.one_rule_undecidable
#audit_axioms_strict UND.one_rule_undecidable
#print axioms UND.midP_pos
#audit_axioms_strict UND.midP_pos
#print axioms UND.midP_val
#audit_axioms_strict UND.midP_val
#print axioms UND.computable_midP
#audit_axioms_strict UND.computable_midP
#print axioms UND.promiseUndecidable_of_noiseDiagram
#audit_axioms_strict UND.promiseUndecidable_of_noiseDiagram
#print axioms UND.corollaryNineFour_of_theoremA
#audit_axioms_strict UND.corollaryNineFour_of_theoremA
#print axioms UND.oneRuleUndecidable_of_corollary
#audit_axioms_strict UND.oneRuleUndecidable_of_corollary
#print axioms UND.Windows.ell_add_one
#audit_axioms_strict UND.Windows.ell_add_one
#print axioms UND.Windows.ell_pos
#audit_axioms_strict UND.Windows.ell_pos
#print axioms UND.Windows.ell_succ
#audit_axioms_strict UND.Windows.ell_succ
#print axioms UND.Windows.ell_mono
#audit_axioms_strict UND.Windows.ell_mono
#print axioms UND.Windows.seven_le_ell
#audit_axioms_strict UND.Windows.seven_le_ell
#print axioms UND.Windows.primrec_ell
#audit_axioms_strict UND.Windows.primrec_ell
#print axioms UND.Windows.computable_loP
#audit_axioms_strict UND.Windows.computable_loP
#print axioms UND.Windows.computable_hiP
#audit_axioms_strict UND.Windows.computable_hiP
#print axioms UND.Windows.presents_lo
#audit_axioms_strict UND.Windows.presents_lo
#print axioms UND.Windows.presents_hi
#audit_axioms_strict UND.Windows.presents_hi
#print axioms UND.Windows.ell_gap
#audit_axioms_strict UND.Windows.ell_gap
#print axioms UND.Windows.hi_lt_lo
#audit_axioms_strict UND.Windows.hi_lt_lo
#print axioms UND.Windows.isWindowFamily_windows
#audit_axioms_strict UND.Windows.isWindowFamily_windows
#print axioms UND.Param.K_eq
#audit_axioms_strict UND.Param.K_eq
#print axioms UND.Param.q_eq
#audit_axioms_strict UND.Param.q_eq
#print axioms UND.Param.h_eq
#audit_axioms_strict UND.Param.h_eq
#print axioms UND.Param.q_lt_two_h
#audit_axioms_strict UND.Param.q_lt_two_h
#print axioms UND.Param.q_sub_h
#audit_axioms_strict UND.Param.q_sub_h
#print axioms UND.Param.two_h_sub_q
#audit_axioms_strict UND.Param.two_h_sub_q
#print axioms UND.Param.V_eq
#audit_axioms_strict UND.Param.V_eq
#print axioms UND.Param.lam_eq
#audit_axioms_strict UND.Param.lam_eq
#print axioms UND.Param.M_eq
#audit_axioms_strict UND.Param.M_eq
#print axioms UND.Param.q_sub_h_add_one
#audit_axioms_strict UND.Param.q_sub_h_add_one
#print axioms UND.Param.psi_sum
#audit_axioms_strict UND.Param.psi_sum
#print axioms UND.Param.gain_zero_good
#audit_axioms_strict UND.Param.gain_zero_good
#print axioms UND.Param.gain_i_good
#audit_axioms_strict UND.Param.gain_i_good
#print axioms UND.Param.gain_zero_worst
#audit_axioms_strict UND.Param.gain_zero_worst
#print axioms UND.Param.gain_i_worst
#audit_axioms_strict UND.Param.gain_i_worst
#print axioms UND.Param.rho_values
#audit_axioms_strict UND.Param.rho_values
#print axioms UND.Param.A0_eq
#audit_axioms_strict UND.Param.A0_eq
#print axioms UND.Param.spancount
#audit_axioms_strict UND.Param.spancount
#print axioms UND.Param.spancount'
#audit_axioms_strict UND.Param.spancount'
#print axioms UND.Param.Omega_eq
#audit_axioms_strict UND.Param.Omega_eq
#print axioms UND.Param.H0_eq
#audit_axioms_strict UND.Param.H0_eq
#print axioms UND.Param.rare_edges
#audit_axioms_strict UND.Param.rare_edges
#print axioms UND.Param.Delta_eq
#audit_axioms_strict UND.Param.Delta_eq
#print axioms UND.Param.roles_le
#audit_axioms_strict UND.Param.roles_le
#print axioms UND.Param.degree_le
#audit_axioms_strict UND.Param.degree_le
#print axioms UND.Param.rare_degree_lt
#audit_axioms_strict UND.Param.rare_degree_lt
#print axioms UND.Param.two_geom_le
#audit_axioms_strict UND.Param.two_geom_le
#print axioms UND.Param.four_le_Kmem_pow
#audit_axioms_strict UND.Param.four_le_Kmem_pow
#print axioms UND.Param.parents_le
#audit_axioms_strict UND.Param.parents_le
#print axioms UND.Param.Delta_pos
#audit_axioms_strict UND.Param.Delta_pos
#print axioms UND.Param.Kmem_pos
#audit_axioms_strict UND.Param.Kmem_pos
#print axioms UND.Param.Khist_pos
#audit_axioms_strict UND.Param.Khist_pos
#print axioms UND.Param.cden_pos
#audit_axioms_strict UND.Param.cden_pos
#print axioms UND.Param.floor_zB
#audit_axioms_strict UND.Param.floor_zB
#print axioms UND.Param.floor_uB
#audit_axioms_strict UND.Param.floor_uB
#print axioms UND.Param.floor_wB
#audit_axioms_strict UND.Param.floor_wB
#print axioms UND.Param.two_zpow_neg
#audit_axioms_strict UND.Param.two_zpow_neg
#print axioms UND.Param.zB_eq
#audit_axioms_strict UND.Param.zB_eq
#print axioms UND.Param.uB_eq
#audit_axioms_strict UND.Param.uB_eq
#print axioms UND.Param.wB_eq
#audit_axioms_strict UND.Param.wB_eq
#print axioms UND.Param.four_inv_le
#audit_axioms_strict UND.Param.four_inv_le
#print axioms UND.Param.eta_lt
#audit_axioms_strict UND.Param.eta_lt
#print axioms UND.Param.three_inv_lt
#audit_axioms_strict UND.Param.three_inv_lt
#print axioms UND.Param.w_52386
#audit_axioms_strict UND.Param.w_52386
#print axioms UND.Param.w_52385
#audit_axioms_strict UND.Param.w_52385
#print axioms UND.Param.z_52386
#audit_axioms_strict UND.Param.z_52386
#print axioms UND.Param.u_52386
#audit_axioms_strict UND.Param.u_52386
#print axioms UND.Param.B_52386
#audit_axioms_strict UND.Param.B_52386
#print axioms UND.Param.mem_target
#audit_axioms_strict UND.Param.mem_target
#print axioms UND.Param.hist_target
#audit_axioms_strict UND.Param.hist_target
#print axioms UND.Param.mem_target_lower
#audit_axioms_strict UND.Param.mem_target_lower
#print axioms UND.Param.bsearch_52386
#audit_axioms_strict UND.Param.bsearch_52386
#print axioms UND.Param.not_bsearch_of_lt
#audit_axioms_strict UND.Param.not_bsearch_of_lt
#print axioms UND.Param.exists_bsearch
#audit_axioms_strict UND.Param.exists_bsearch
#print axioms UND.Param.bsearch_kParam
#audit_axioms_strict UND.Param.bsearch_kParam
#print axioms UND.Param.kParam_eq
#audit_axioms_strict UND.Param.kParam_eq
#print axioms UND.Chart.black_child_ff
#audit_axioms_strict UND.Chart.black_child_ff
#print axioms UND.Chart.black_child_tt
#audit_axioms_strict UND.Chart.black_child_tt
#print axioms UND.Chart.black_child_tf
#audit_axioms_strict UND.Chart.black_child_tf
#print axioms UND.Chart.black_child_ft
#audit_axioms_strict UND.Chart.black_child_ft
#print axioms UND.Chart.chain_black
#audit_axioms_strict UND.Chart.chain_black
#print axioms UND.Chart.black_rank_compare
#audit_axioms_strict UND.Chart.black_rank_compare
#print axioms UND.Chart.exists_rank
#audit_axioms_strict UND.Chart.exists_rank
#print axioms UND.Chart.cutoff_of_filter
#audit_axioms_strict UND.Chart.cutoff_of_filter
#print axioms UND.CA.isProbabilityMeasure_uniformLaw
#audit_axioms_strict UND.CA.isProbabilityMeasure_uniformLaw
#print axioms UND.CA.uniformLaw_singleton
#audit_axioms_strict UND.CA.uniformLaw_singleton
#print axioms UND.CA.isProbabilityMeasure_noiseSite
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseSite
#print axioms UND.CA.isProbabilityMeasure_noiseLaw
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseLaw
#print axioms UND.CA.isProbabilityMeasure_noiseLaw₂
#audit_axioms_strict UND.CA.isProbabilityMeasure_noiseLaw₂
#print axioms UND.CA.apply_congr
#audit_axioms_strict UND.CA.apply_congr
#print axioms UND.CA.measurable_of_local
#audit_axioms_strict UND.CA.measurable_of_local
#print axioms UND.CA.measurable_apply_apply
#audit_axioms_strict UND.CA.measurable_apply_apply
#print axioms UND.CA.measurable_apply
#audit_axioms_strict UND.CA.measurable_apply
#print axioms UND.CA.measurable_run
#audit_axioms_strict UND.CA.measurable_run
#print axioms UND.CA.isProbabilityMeasure_law
#audit_axioms_strict UND.CA.isProbabilityMeasure_law
#print axioms UND.CA.law_zero
#audit_axioms_strict UND.CA.law_zero
#print axioms UND.CA.law_apply_eq_lintegral
#audit_axioms_strict UND.CA.law_apply_eq_lintegral
#print axioms UND.CA.law_dirac
#audit_axioms_strict UND.CA.law_dirac
#print axioms UND.CA.noiseLaw_flags_eq
#audit_axioms_strict UND.CA.noiseLaw_flags_eq
#print axioms UND.CA.run_succ
#audit_axioms_strict UND.CA.run_succ
#print axioms UND.CA.run_one
#audit_axioms_strict UND.CA.run_one
#print axioms UND.CA.run_succ_shift
#audit_axioms_strict UND.CA.run_succ_shift
#print axioms UND.CA.measurable_slice0
#audit_axioms_strict UND.CA.measurable_slice0
#print axioms UND.CA.measurable_shiftN
#audit_axioms_strict UND.CA.measurable_shiftN
#print axioms UND.CA.measurable_splitN
#audit_axioms_strict UND.CA.measurable_splitN
#print axioms UND.CA.measurable_update
#audit_axioms_strict UND.CA.measurable_update
#print axioms UND.CA.splitIdx_injective
#audit_axioms_strict UND.CA.splitIdx_injective
#print axioms UND.CA.noiseLaw_map_splitN
#audit_axioms_strict UND.CA.noiseLaw_map_splitN
#print axioms UND.CA.noiseLaw_map_slice0
#audit_axioms_strict UND.CA.noiseLaw_map_slice0
#print axioms UND.CA.noiseSite_map_eq
#audit_axioms_strict UND.CA.noiseSite_map_eq
#print axioms UND.CA.law_dirac_one
#audit_axioms_strict UND.CA.law_dirac_one
#print axioms UND.CA.law_succ'
#audit_axioms_strict UND.CA.law_succ'
#print axioms UND.CA.law_succ
#audit_axioms_strict UND.CA.law_succ
#print axioms UND.CA.siteLaw_pos
#audit_axioms_strict UND.CA.siteLaw_pos
#print axioms UND.CA.continuous_restrictWindow
#audit_axioms_strict UND.CA.continuous_restrictWindow
#print axioms UND.CA.measurable_restrictWindow
#audit_axioms_strict UND.CA.measurable_restrictWindow
#print axioms UND.CA.measurableSet_cyl
#audit_axioms_strict UND.CA.measurableSet_cyl
#print axioms UND.CA.integral_cylIndicator
#audit_axioms_strict UND.CA.integral_cylIndicator
#print axioms UND.CA.not_ergodic_of_memoryFrom
#audit_axioms_strict UND.CA.not_ergodic_of_memoryFrom
#print axioms UND.CA.abs_le_dtv
#audit_axioms_strict UND.CA.abs_le_dtv
#print axioms UND.CA.dtv_le_of
#audit_axioms_strict UND.CA.dtv_le_of
#print axioms UND.CA.dtv_nonneg
#audit_axioms_strict UND.CA.dtv_nonneg
#print axioms UND.CA.dtv_comm
#audit_axioms_strict UND.CA.dtv_comm
#print axioms UND.CA.dtv_le_one
#audit_axioms_strict UND.CA.dtv_le_one
#print axioms UND.CA.deltaO_nonneg
#audit_axioms_strict UND.CA.deltaO_nonneg
#print axioms UND.CA.dtv_le_deltaO
#audit_axioms_strict UND.CA.dtv_le_deltaO
#print axioms UND.CA.deltaO_le_of
#audit_axioms_strict UND.CA.deltaO_le_of
#print axioms UND.CA.abs_toReal_sub_le_of_subset
#audit_axioms_strict UND.CA.abs_toReal_sub_le_of_subset
#print axioms UND.CA.law_dirac_cyl
#audit_axioms_strict UND.CA.law_dirac_cyl
#print axioms UND.CA.dtv_law_dirac_le
#audit_axioms_strict UND.CA.dtv_law_dirac_le
#print axioms UND.CA.deltaO_le_disagree
#audit_axioms_strict UND.CA.deltaO_le_disagree
#print axioms UND.CA.forgets_of_coupling
#audit_axioms_strict UND.CA.forgets_of_coupling
#print axioms UND.CA.continuous_of_local
#audit_axioms_strict UND.CA.continuous_of_local
#print axioms UND.CA.continuous_apply_apply
#audit_axioms_strict UND.CA.continuous_apply_apply
#print axioms UND.CA.continuous_applyMap
#audit_axioms_strict UND.CA.continuous_applyMap
#print axioms UND.CA.continuous_run
#audit_axioms_strict UND.CA.continuous_run
#print axioms UND.CA.integral_law_dirac
#audit_axioms_strict UND.CA.integral_law_dirac
#print axioms UND.CA.integral_law
#audit_axioms_strict UND.CA.integral_law
#print axioms UND.CA.continuous_Phi
#audit_axioms_strict UND.CA.continuous_Phi
#print axioms UND.CA.integral_Phi_law
#audit_axioms_strict UND.CA.integral_Phi_law
#print axioms UND.CA.isProbabilityMeasure_cesaro
#audit_axioms_strict UND.CA.isProbabilityMeasure_cesaro
#print axioms UND.CA.integral_cesaro
#audit_axioms_strict UND.CA.integral_cesaro
#print axioms UND.CA.isStationary_of_cesaro_limit
#audit_axioms_strict UND.CA.isStationary_of_cesaro_limit
#print axioms UND.CA.exists_cesaro_limit
#audit_axioms_strict UND.CA.exists_cesaro_limit
#print axioms UND.CA.exists_stationary
#audit_axioms_strict UND.CA.exists_stationary
#print axioms UND.CA.exists_window_approx
#audit_axioms_strict UND.CA.exists_window_approx
#print axioms UND.CA.integral_window
#audit_axioms_strict UND.CA.integral_window
#print axioms UND.CA.weakTendsto_of_cyl
#audit_axioms_strict UND.CA.weakTendsto_of_cyl
#print axioms UND.CA.weakTendsto_iff_cyl
#audit_axioms_strict UND.CA.weakTendsto_iff_cyl
#print axioms UND.CA.weakTendsto_iff_dtv
#audit_axioms_strict UND.CA.weakTendsto_iff_dtv
#print axioms UND.CA.measurable_shift
#audit_axioms_strict UND.CA.measurable_shift
#print axioms UND.CA.continuous_shift
#audit_axioms_strict UND.CA.continuous_shift
#print axioms UND.CA.apply_shift
#audit_axioms_strict UND.CA.apply_shift
#print axioms UND.CA.measurable_shiftNoise
#audit_axioms_strict UND.CA.measurable_shiftNoise
#print axioms UND.CA.run_shift
#audit_axioms_strict UND.CA.run_shift
#print axioms UND.CA.noiseLaw_map_shiftNoise
#audit_axioms_strict UND.CA.noiseLaw_map_shiftNoise
#print axioms UND.CA.law_map_shift
#audit_axioms_strict UND.CA.law_map_shift
#print axioms UND.CA.isTI_law
#audit_axioms_strict UND.CA.isTI_law
#print axioms UND.CA.isTI_cesaro
#audit_axioms_strict UND.CA.isTI_cesaro
#print axioms UND.CA.isTI_of_weakTendsto
#audit_axioms_strict UND.CA.isTI_of_weakTendsto
#print axioms UND.CA.isTI_of_cesaro_limit
#audit_axioms_strict UND.CA.isTI_of_cesaro_limit
#print axioms UND.CA.measurable_law_dirac_apply
#audit_axioms_strict UND.CA.measurable_law_dirac_apply
#print axioms UND.CA.law_toReal_eq_integral
#audit_axioms_strict UND.CA.law_toReal_eq_integral
#print axioms UND.CA.abs_law_sub_zero_le
#audit_axioms_strict UND.CA.abs_law_sub_zero_le
#print axioms UND.CA.dtv_law_le
#audit_axioms_strict UND.CA.dtv_law_le
#print axioms UND.CA.law_of_stationary
#audit_axioms_strict UND.CA.law_of_stationary
#print axioms UND.CA.ergodic_of_forgets
#audit_axioms_strict UND.CA.ergodic_of_forgets
#print axioms UND.CA.two_stationary_of_memory
#audit_axioms_strict UND.CA.two_stationary_of_memory
#print axioms UND.CA.hasTwoTIStationaryLaws_of_memory
#audit_axioms_strict UND.CA.hasTwoTIStationaryLaws_of_memory
#print axioms UND.CA.not_ergodic_of_two
#audit_axioms_strict UND.CA.not_ergodic_of_two
#print axioms UND.CA.noiseDiagram_clauses
#audit_axioms_strict UND.CA.noiseDiagram_clauses
#print axioms UND.Param.DeltaRareOf_pos
#audit_axioms_strict UND.Param.DeltaRareOf_pos
#print axioms UND.Param.KrareOf_pos
#audit_axioms_strict UND.Param.KrareOf_pos
#print axioms UND.Param.Krare_pos
#audit_axioms_strict UND.Param.Krare_pos
#print axioms UND.Param.C_pos
#audit_axioms_strict UND.Param.C_pos
#print axioms UND.Param.C_eq_inv
#audit_axioms_strict UND.Param.C_eq_inv
#print axioms UND.Param.epsStarOf_pos
#audit_axioms_strict UND.Param.epsStarOf_pos
#print axioms UND.Param.epsStarOf_le_C
#audit_axioms_strict UND.Param.epsStarOf_le_C
#print axioms UND.Param.epsStarOf_le_mem
#audit_axioms_strict UND.Param.epsStarOf_le_mem
#print axioms UND.Param.epsStarOf_le_hist
#audit_axioms_strict UND.Param.epsStarOf_le_hist
#print axioms UND.Param.epsStarOf_le_rare
#audit_axioms_strict UND.Param.epsStarOf_le_rare
#print axioms UND.Param.epsStar_pos
#audit_axioms_strict UND.Param.epsStar_pos
#print axioms UND.Param.epsStar_le_C
#audit_axioms_strict UND.Param.epsStar_le_C
#print axioms UND.Param.epsStar_le_mem
#audit_axioms_strict UND.Param.epsStar_le_mem
#print axioms UND.Param.epsStar_le_hist
#audit_axioms_strict UND.Param.epsStar_le_hist
#print axioms UND.Param.Krare_eq
#audit_axioms_strict UND.Param.Krare_eq
#print axioms UND.Param.epsStar_le_rare
#audit_axioms_strict UND.Param.epsStar_le_rare
#print axioms UND.Param.ell_cast
#audit_axioms_strict UND.Param.ell_cast
#print axioms UND.Param.exists_n0_general
#audit_axioms_strict UND.Param.exists_n0_general
#print axioms UND.Param.exists_n0Search
#audit_axioms_strict UND.Param.exists_n0Search
#print axioms UND.Param.n0Search_n0Param
#audit_axioms_strict UND.Param.n0Search_n0Param
#print axioms UND.Param.n0Param_ge
#audit_axioms_strict UND.Param.n0Param_ge
#print axioms UND.Param.isWindowFamily_final
#audit_axioms_strict UND.Param.isWindowFamily_final
#print axioms UND.Param.hi_lt_of_search
#audit_axioms_strict UND.Param.hi_lt_of_search
#print axioms UND.Param.hiF_lt_epsStar
#audit_axioms_strict UND.Param.hiF_lt_epsStar
#print axioms UND.Param.window_subset
#audit_axioms_strict UND.Param.window_subset
#print axioms UND.Param.le_C_div_100
#audit_axioms_strict UND.Param.le_C_div_100
#print axioms UND.Param.a_ge
#audit_axioms_strict UND.Param.a_ge
#print axioms UND.Param.ruler_margins
#audit_axioms_strict UND.Param.ruler_margins
#print axioms UND.Contour.GroupedSystem.not_NF_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.not_NF_of_UN
#print axioms UND.Contour.GroupedSystem.rk_induction
#audit_axioms_strict UND.Contour.GroupedSystem.rk_induction
#print axioms UND.Contour.GroupedSystem.eq_of_reach_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.eq_of_reach_of_isTerm
#print axioms UND.Contour.GroupedSystem.reach_sup
#audit_axioms_strict UND.Contour.GroupedSystem.reach_sup
#print axioms UND.Contour.GroupedSystem.reach_un
#audit_axioms_strict UND.Contour.GroupedSystem.reach_un
#print axioms UND.Contour.GroupedSystem.term_trans
#audit_axioms_strict UND.Contour.GroupedSystem.term_trans
#print axioms UND.Contour.GroupedSystem.term_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.term_of_isTerm
#print axioms UND.Contour.GroupedSystem.term_isTerm_iff
#audit_axioms_strict UND.Contour.GroupedSystem.term_isTerm_iff
#print axioms UND.Contour.GroupedSystem.term_of_sup
#audit_axioms_strict UND.Contour.GroupedSystem.term_of_sup
#print axioms UND.Contour.GroupedSystem.term_sup_iff
#audit_axioms_strict UND.Contour.GroupedSystem.term_sup_iff
#print axioms UND.Contour.GroupedSystem.term_un_iff
#audit_axioms_strict UND.Contour.GroupedSystem.term_un_iff
#print axioms UND.Contour.GroupedSystem.g_of_NF
#audit_axioms_strict UND.Contour.GroupedSystem.g_of_NF
#print axioms UND.Contour.GroupedSystem.g_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.g_of_UN
#print axioms UND.Contour.GroupedSystem.rk_g
#audit_axioms_strict UND.Contour.GroupedSystem.rk_g
#print axioms UND.Contour.GroupedSystem.reach_g
#audit_axioms_strict UND.Contour.GroupedSystem.reach_g
#print axioms UND.Contour.GroupedSystem.gEnd_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_of_step
#print axioms UND.Contour.GroupedSystem.gEnd_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_of_isTerm
#print axioms UND.Contour.GroupedSystem.gBin_of_NF
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_NF
#print axioms UND.Contour.GroupedSystem.gBin_of_UN
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_UN
#print axioms UND.Contour.GroupedSystem.gBin_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gBin_of_isTerm
#print axioms UND.Contour.GroupedSystem.gLen_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_of_step
#print axioms UND.Contour.GroupedSystem.gLen_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_of_isTerm
#print axioms UND.Contour.GroupedSystem.isTerm_of_not
#audit_axioms_strict UND.Contour.GroupedSystem.isTerm_of_not
#print axioms UND.Contour.GroupedSystem.g_induction
#audit_axioms_strict UND.Contour.GroupedSystem.g_induction
#print axioms UND.Contour.GroupedSystem.gEnd_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_isTerm
#print axioms UND.Contour.GroupedSystem.reach_gEnd
#audit_axioms_strict UND.Contour.GroupedSystem.reach_gEnd
#print axioms UND.Contour.GroupedSystem.gEnd_term
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_term
#print axioms UND.Contour.GroupedSystem.exists_term
#audit_axioms_strict UND.Contour.GroupedSystem.exists_term
#print axioms UND.Contour.GroupedSystem.gEnd_psi
#audit_axioms_strict UND.Contour.GroupedSystem.gEnd_psi
#print axioms UND.Contour.GroupedSystem.gEdges_of_step
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_of_step
#print axioms UND.Contour.GroupedSystem.gEdges_of_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_of_isTerm
#print axioms UND.Contour.GroupedSystem.gEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_card_le
#print axioms UND.Contour.GroupedSystem.gEdges_spec
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_spec
#print axioms UND.Contour.GroupedSystem.reach_mono
#audit_axioms_strict UND.Contour.GroupedSystem.reach_mono
#print axioms UND.Contour.GroupedSystem.reach_symm
#audit_axioms_strict UND.Contour.GroupedSystem.reach_symm
#print axioms UND.Contour.GroupedSystem.gEdges_reach
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_reach
#print axioms UND.Contour.GroupedSystem.pEnd_isTerm
#audit_axioms_strict UND.Contour.GroupedSystem.pEnd_isTerm
#print axioms UND.Contour.GroupedSystem.pGrp_term
#audit_axioms_strict UND.Contour.GroupedSystem.pGrp_term
#print axioms UND.Contour.GroupedSystem.pGrp_term_root
#audit_axioms_strict UND.Contour.GroupedSystem.pGrp_term_root
#print axioms UND.Contour.GroupedSystem.pole_psi
#audit_axioms_strict UND.Contour.GroupedSystem.pole_psi
#print axioms UND.Contour.GroupedSystem.rel_symm
#audit_axioms_strict UND.Contour.GroupedSystem.rel_symm
#print axioms UND.Contour.GroupedSystem.rel_of_term
#audit_axioms_strict UND.Contour.GroupedSystem.rel_of_term
#print axioms UND.Contour.GroupedSystem.mem_frontB_true
#audit_axioms_strict UND.Contour.GroupedSystem.mem_frontB_true
#print axioms UND.Contour.GroupedSystem.mem_frontB_false
#audit_axioms_strict UND.Contour.GroupedSystem.mem_frontB_false
#print axioms UND.Contour.GroupedSystem.rel_frontB_mono
#audit_axioms_strict UND.Contour.GroupedSystem.rel_frontB_mono
#print axioms UND.Contour.GroupedSystem.rel_split
#audit_axioms_strict UND.Contour.GroupedSystem.rel_split
#print axioms UND.Contour.GroupedSystem.ov_frontU
#audit_axioms_strict UND.Contour.GroupedSystem.ov_frontU
#print axioms UND.Contour.GroupedSystem.rel_frontU
#audit_axioms_strict UND.Contour.GroupedSystem.rel_frontU
#print axioms UND.Contour.GroupedSystem.stepB_exists
#audit_axioms_strict UND.Contour.GroupedSystem.stepB_exists
#print axioms UND.Contour.GroupedSystem.sum_insert_le'
#audit_axioms_strict UND.Contour.GroupedSystem.sum_insert_le'
#print axioms UND.Contour.GroupedSystem.meas_frontB_lt
#audit_axioms_strict UND.Contour.GroupedSystem.meas_frontB_lt
#print axioms UND.Contour.GroupedSystem.meas_frontU_lt
#audit_axioms_strict UND.Contour.GroupedSystem.meas_frontU_lt
#print axioms UND.Contour.GroupedSystem.frontB_reach
#audit_axioms_strict UND.Contour.GroupedSystem.frontB_reach
#print axioms UND.Contour.GroupedSystem.frontU_reach
#audit_axioms_strict UND.Contour.GroupedSystem.frontU_reach
#print axioms UND.Contour.GroupedSystem.exists_poles
#audit_axioms_strict UND.Contour.GroupedSystem.exists_poles
#print axioms UND.Contour.GroupedSystem.exists_bij
#audit_axioms_strict UND.Contour.GroupedSystem.exists_bij
#print axioms UND.Contour.GroupedSystem.grouped_terminal_estimate
#audit_axioms_strict UND.Contour.GroupedSystem.grouped_terminal_estimate
#print axioms UND.Contour.GroupedSystem.pEdges_reach
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_reach
#print axioms UND.Contour.GroupedSystem.pEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_card_le
#print axioms UND.Contour.GroupedSystem.armEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.armEdges_card_le
#print axioms UND.Contour.GroupedSystem.pEdges_subset_witness
#audit_axioms_strict UND.Contour.GroupedSystem.pEdges_subset_witness
#print axioms UND.Contour.GroupedSystem.grpEdge_mem_witness
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdge_mem_witness
#print axioms UND.Contour.GroupedSystem.witness_connected
#audit_axioms_strict UND.Contour.GroupedSystem.witness_connected
#print axioms UND.Contour.GroupedSystem.root_mem_witness
#audit_axioms_strict UND.Contour.GroupedSystem.root_mem_witness
#print axioms UND.Contour.GroupedSystem.two_le_card_of_bound
#audit_axioms_strict UND.Contour.GroupedSystem.two_le_card_of_bound
#print axioms UND.Contour.GroupedSystem.hosc_singleton
#audit_axioms_strict UND.Contour.GroupedSystem.hosc_singleton
#print axioms UND.Contour.GroupedSystem.singleton_two_le
#audit_axioms_strict UND.Contour.GroupedSystem.singleton_two_le
#print axioms UND.Contour.GroupedSystem.time_le_of_edgeReach
#audit_axioms_strict UND.Contour.GroupedSystem.time_le_of_edgeReach
#print axioms UND.Contour.GroupedSystem.gEdges_crossing_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.gEdges_crossing_card_le
#print axioms UND.Contour.GroupedSystem.armEdges_crossing_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.armEdges_crossing_card_le
#print axioms UND.Contour.GroupedSystem.witness_reach
#audit_axioms_strict UND.Contour.GroupedSystem.witness_reach
#print axioms UND.Contour.GroupedSystem.time_le_of_reach
#audit_axioms_strict UND.Contour.GroupedSystem.time_le_of_reach
#print axioms UND.Contour.GroupedSystem.witness_span
#audit_axioms_strict UND.Contour.GroupedSystem.witness_span
#print axioms UND.Contour.GroupedSystem.polebound_of_int
#audit_axioms_strict UND.Contour.GroupedSystem.polebound_of_int
#print axioms UND.Contour.GroupedSystem.grouped_terminal_estimate_paper
#audit_axioms_strict UND.Contour.GroupedSystem.grouped_terminal_estimate_paper
#print axioms UND.CA.continuous_update
#audit_axioms_strict UND.CA.continuous_update
#print axioms UND.CA.flow_succ'
#audit_axioms_strict UND.CA.flow_succ'
#print axioms UND.CA.pullback_succ
#audit_axioms_strict UND.CA.pullback_succ
#print axioms UND.CA.pullback_mono
#audit_axioms_strict UND.CA.pullback_mono
#print axioms UND.CA.history_succ
#audit_axioms_strict UND.CA.history_succ
#print axioms UND.CA.history_zero
#audit_axioms_strict UND.CA.history_zero
#print axioms UND.CA.exists_complete_of_pullback
#audit_axioms_strict UND.CA.exists_complete_of_pullback
#print axioms UND.CA.exists_complete
#audit_axioms_strict UND.CA.exists_complete
#print axioms UND.CA.pullback_eventually_singleton_of_unique
#audit_axioms_strict UND.CA.pullback_eventually_singleton_of_unique
#print axioms UND.CA.pullbackEventuallySingleton_of_unique
#audit_axioms_strict UND.CA.pullbackEventuallySingleton_of_unique
#print axioms UND.CA.run_congr_cone
#audit_axioms_strict UND.CA.run_congr_cone
#print axioms UND.CA.measurableSet_disagree
#audit_axioms_strict UND.CA.measurableSet_disagree
#print axioms UND.CA.measurable_tau
#audit_axioms_strict UND.CA.measurable_tau
#print axioms UND.CA.noiseLaw₂_map_tau
#audit_axioms_strict UND.CA.noiseLaw₂_map_tau
#print axioms UND.CA.flow_eq_run
#audit_axioms_strict UND.CA.flow_eq_run
#print axioms UND.CA.pullFail_eq_preimage
#audit_axioms_strict UND.CA.pullFail_eq_preimage
#print axioms UND.CA.measurableSet_pullFail
#audit_axioms_strict UND.CA.measurableSet_pullFail
#print axioms UND.CA.noiseLaw₂_pullFail
#audit_axioms_strict UND.CA.noiseLaw₂_pullFail
#print axioms UND.CA.pullFail_antitone
#audit_axioms_strict UND.CA.pullFail_antitone
#print axioms UND.CA.forgets_of_unique
#audit_axioms_strict UND.CA.forgets_of_unique
#print axioms UND.CA.ergodic_of_unique
#audit_axioms_strict UND.CA.ergodic_of_unique
#print axioms UND.Param.Kmem_sqrt_C
#audit_axioms_strict UND.Param.Kmem_sqrt_C
#print axioms UND.Param.etaHat_pos
#audit_axioms_strict UND.Param.etaHat_pos
#print axioms UND.Param.mem_eta_base
#audit_axioms_strict UND.Param.mem_eta_base
#print axioms UND.Param.mem_eta_base_kParam
#audit_axioms_strict UND.Param.mem_eta_base_kParam
#print axioms UND.Param.mem_gamma_lt
#audit_axioms_strict UND.Param.mem_gamma_lt
#print axioms UND.Param.mem_series_lt
#audit_axioms_strict UND.Param.mem_series_lt
#print axioms UND.Param.raw_base_lt
#audit_axioms_strict UND.Param.raw_base_lt
#print axioms UND.Param.rpow_sixteenth_lt
#audit_axioms_strict UND.Param.rpow_sixteenth_lt
#print axioms UND.Param.rare_base_lt
#audit_axioms_strict UND.Param.rare_base_lt
#print axioms UND.Param.rare_base_lt_epsStarOf
#audit_axioms_strict UND.Param.rare_base_lt_epsStarOf
#print axioms UND.Counting.finite_connected
#audit_axioms_strict UND.Counting.finite_connected
#print axioms UND.Counting.mem_connSets
#audit_axioms_strict UND.Counting.mem_connSets
#print axioms UND.Counting.connSets_spec
#audit_axioms_strict UND.Counting.connSets_spec
#print axioms UND.Counting.card_connSets_le
#audit_axioms_strict UND.Counting.card_connSets_le
#print axioms UND.Counting.vertsOf_spec
#audit_axioms_strict UND.Counting.vertsOf_spec
#print axioms UND.Counting.card_enc_le
#audit_axioms_strict UND.Counting.card_enc_le
#print axioms UND.Counting.enc_term
#audit_axioms_strict UND.Counting.enc_term
#print axioms UND.Counting.card_encLe_le
#audit_axioms_strict UND.Counting.card_encLe_le
#print axioms UND.Counting.mem_encLe
#audit_axioms_strict UND.Counting.mem_encLe
#print axioms UND.Counting.four_mul_pow_le
#audit_axioms_strict UND.Counting.four_mul_pow_le
#print axioms UND.Counting.card_encLe_Kmem
#audit_axioms_strict UND.Counting.card_encLe_Kmem
#print axioms UND.Counting.four_le_Kmem_pow_of_le
#audit_axioms_strict UND.Counting.four_le_Kmem_pow_of_le
#print axioms UND.Counting.four_le_KrareOf_pow
#audit_axioms_strict UND.Counting.four_le_KrareOf_pow
#print axioms UND.Counting.card_encLe_KrareOf
#audit_axioms_strict UND.Counting.card_encLe_KrareOf
#print axioms UND.Counting.measure_biUnion_le_card_mul
#audit_axioms_strict UND.Counting.measure_biUnion_le_card_mul
#print axioms UND.Counting.measure_le_tsum_groups
#audit_axioms_strict UND.Counting.measure_le_tsum_groups
#print axioms UND.Counting.tsum_ofReal_pow_succ
#audit_axioms_strict UND.Counting.tsum_ofReal_pow_succ
#print axioms UND.Counting.measure_le_ofReal_tsum
#audit_axioms_strict UND.Counting.measure_le_ofReal_tsum
#print axioms UND.Counting.connectedAt_image
#audit_axioms_strict UND.Counting.connectedAt_image
#print axioms UND.Counting.connectedAt_filter_not_diag
#audit_axioms_strict UND.Counting.connectedAt_filter_not_diag
#print axioms UND.Counting.card_image_filter_le
#audit_axioms_strict UND.Counting.card_image_filter_le
#print axioms UND.Contour.GroupedSystem.gLen_le_two_gBin
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_le_two_gBin
#print axioms UND.Contour.GroupedSystem.pLen_le_two_pBin
#audit_axioms_strict UND.Contour.GroupedSystem.pLen_le_two_pBin
#print axioms UND.Contour.GroupedSystem.gLen_le_three_gBin
#audit_axioms_strict UND.Contour.GroupedSystem.gLen_le_three_gBin
#print axioms UND.Contour.GroupedSystem.pLen_le_three_pBin
#audit_axioms_strict UND.Contour.GroupedSystem.pLen_le_three_pBin
#print axioms UND.Contour.GroupedSystem.witness_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.witness_card_le
#print axioms UND.Contour.GroupedSystem.grpEdges_card_le
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdges_card_le
#print axioms UND.Contour.GroupedSystem.witness_isEncoding
#audit_axioms_strict UND.Contour.GroupedSystem.witness_isEncoding
#print axioms UND.Rule.card_Prov
#audit_axioms_strict UND.Rule.card_Prov
#print axioms UND.Rule.provOff_mem
#audit_axioms_strict UND.Rule.provOff_mem
#print axioms UND.Rule.quorum_unique
#audit_axioms_strict UND.Rule.quorum_unique
#print axioms UND.Rule.quorumPick_eq_some_iff
#audit_axioms_strict UND.Rule.quorumPick_eq_some_iff
#print axioms UND.Rule.quorumPick_eq_none_iff
#audit_axioms_strict UND.Rule.quorumPick_eq_none_iff
#print axioms UND.Rule.FR_eq_some_iff
#audit_axioms_strict UND.Rule.FR_eq_some_iff
#print axioms UND.Rule.FR_eq_none_iff
#audit_axioms_strict UND.Rule.FR_eq_none_iff
#print axioms UND.Rule.chk_chart
#audit_axioms_strict UND.Rule.chk_chart
#print axioms UND.Rule.FR_cloned
#audit_axioms_strict UND.Rule.FR_cloned
#print axioms UND.Rule.chk_translate
#audit_axioms_strict UND.Rule.chk_translate
#print axioms UND.Rule.quorumCount_translate
#audit_axioms_strict UND.Rule.quorumCount_translate
#print axioms UND.Rule.FR_translate
#audit_axioms_strict UND.Rule.FR_translate
#print axioms UND.Rule.FR_iter_translate
#audit_axioms_strict UND.Rule.FR_iter_translate
#print axioms UND.Rule.chk_congr
#audit_axioms_strict UND.Rule.chk_congr
#print axioms UND.Rule.FR_local
#audit_axioms_strict UND.Rule.FR_local
#print axioms UND.Rule.mem_box_add
#audit_axioms_strict UND.Rule.mem_box_add
#print axioms UND.Rule.FR_iter_local
#audit_axioms_strict UND.Rule.FR_iter_local
#print axioms UND.Rule.Helper.rep_repr
#audit_axioms_strict UND.Rule.Helper.rep_repr
#print axioms UND.Rule.Helper.card_rep
#audit_axioms_strict UND.Rule.Helper.card_rep
#print axioms UND.Rule.drvA_translate
#audit_axioms_strict UND.Rule.drvA_translate
#print axioms UND.Rule.drvQ_translate
#audit_axioms_strict UND.Rule.drvQ_translate
#print axioms UND.Rule.Jf_translate
#audit_axioms_strict UND.Rule.Jf_translate
#print axioms UND.Rule.hcount_translate
#audit_axioms_strict UND.Rule.hcount_translate
#print axioms UND.Rule.lcount_translate
#audit_axioms_strict UND.Rule.lcount_translate
#print axioms UND.Rule.Pin_translate
#audit_axioms_strict UND.Rule.Pin_translate
#print axioms UND.Rule.proposal_translate
#audit_axioms_strict UND.Rule.proposal_translate
#print axioms UND.Rule.card_nbhdA_le
#audit_axioms_strict UND.Rule.card_nbhdA_le
#print axioms UND.Rule.card_box
#audit_axioms_strict UND.Rule.card_box
#print axioms UND.Rule.card_nbhdQ
#audit_axioms_strict UND.Rule.card_nbhdQ
#print axioms UND.Rule.card_nbhdP_le
#audit_axioms_strict UND.Rule.card_nbhdP_le
#print axioms UND.Rule.drvA_congr
#audit_axioms_strict UND.Rule.drvA_congr
#print axioms UND.Rule.mem_cubeQ
#audit_axioms_strict UND.Rule.mem_cubeQ
#print axioms UND.Rule.drvQ_congr
#audit_axioms_strict UND.Rule.drvQ_congr
#print axioms UND.Rule.proposal_local
#audit_axioms_strict UND.Rule.proposal_local
#print axioms UND.Rule.caOf_apply
#audit_axioms_strict UND.Rule.caOf_apply
#print axioms UND.Rule.card_nbhd_caOf
#audit_axioms_strict UND.Rule.card_nbhd_caOf
#print axioms UND.Rule.ruleCA_apply
#audit_axioms_strict UND.Rule.ruleCA_apply
#print axioms UND.Rule.prop_2_1
#audit_axioms_strict UND.Rule.prop_2_1
#print axioms UND.window_rate
#audit_axioms_strict UND.window_rate
#print axioms UND.noiseDiagram_of_branches
#audit_axioms_strict UND.noiseDiagram_of_branches
#print axioms UND.theoremA_of_branches
#audit_axioms_strict UND.theoremA_of_branches
#print axioms UND.Rule.update_decode
#audit_axioms_strict UND.Rule.update_decode
#print axioms UND.Rule.uniformLaw_decode
#audit_axioms_strict UND.Rule.uniformLaw_decode
#print axioms UND.Rule.swapField_swapField
#audit_axioms_strict UND.Rule.swapField_swapField
#print axioms UND.Rule.card_field_fiber_eq
#audit_axioms_strict UND.Rule.card_field_fiber_eq
#print axioms UND.Rule.card_field_fiber
#audit_axioms_strict UND.Rule.card_field_fiber
#print axioms UND.Rule.uniformLaw_field
#audit_axioms_strict UND.Rule.uniformLaw_field
#print axioms UND.Chart.lanePhase_succ
#audit_axioms_strict UND.Chart.lanePhase_succ
#print axioms UND.Chart.four_pow_eq
#audit_axioms_strict UND.Chart.four_pow_eq
#print axioms UND.Chart.wsum_dvd_sub
#audit_axioms_strict UND.Chart.wsum_dvd_sub
#print axioms UND.Chart.lanePhase_bot
#audit_axioms_strict UND.Chart.lanePhase_bot
#print axioms UND.Chart.lanePhase_bot_eq_zero_iff
#audit_axioms_strict UND.Chart.lanePhase_bot_eq_zero_iff
#print axioms UND.Chart.walls_VW_of_rank
#audit_axioms_strict UND.Chart.walls_VW_of_rank
#print axioms UND.Chart.walls_HW_of_rank
#audit_axioms_strict UND.Chart.walls_HW_of_rank
#print axioms UND.Chart.frameHi_sub_frameLo
#audit_axioms_strict UND.Chart.frameHi_sub_frameLo
#print axioms UND.Chart.exists_prank_le_of_inFrame
#audit_axioms_strict UND.Chart.exists_prank_le_of_inFrame
#print axioms UND.Chart.inFrame_of_isLeftEnd
#audit_axioms_strict UND.Chart.inFrame_of_isLeftEnd
#print axioms UND.Chart.inFrame_of_isRightEnd
#audit_axioms_strict UND.Chart.inFrame_of_isRightEnd
#print axioms UND.Chart.le_of_end_inFrame
#audit_axioms_strict UND.Chart.le_of_end_inFrame
#print axioms UND.Chart.bottom_corner_iff
#audit_axioms_strict UND.Chart.bottom_corner_iff
#print axioms UND.Chart.orig_iff
#audit_axioms_strict UND.Chart.orig_iff
#print axioms UND.Chart.end_iff
#audit_axioms_strict UND.Chart.end_iff
#print axioms UND.Chart.end_gate
#audit_axioms_strict UND.Chart.end_gate
#print axioms UND.Chart.DQuarter.matchE_iff
#audit_axioms_strict UND.Chart.DQuarter.matchE_iff
#print axioms UND.Chart.DQuarter.matchN_iff
#audit_axioms_strict UND.Chart.DQuarter.matchN_iff
#print axioms UND.Chart.DQuarter.toQ_matchE
#audit_axioms_strict UND.Chart.DQuarter.toQ_matchE
#print axioms UND.Chart.DQuarter.toQ_matchN
#audit_axioms_strict UND.Chart.DQuarter.toQ_matchN
#print axioms UND.Chart.DQuarter.H_eq_of_matchE
#audit_axioms_strict UND.Chart.DQuarter.H_eq_of_matchE
#print axioms UND.Chart.DQuarter.V_eq_of_matchN
#audit_axioms_strict UND.Chart.DQuarter.V_eq_of_matchN
#print axioms UND.Chart.isQTiling_toQ
#audit_axioms_strict UND.Chart.isQTiling_toQ
#print axioms UND.Chart.H_row_const
#audit_axioms_strict UND.Chart.H_row_const
#print axioms UND.Chart.V_col_const
#audit_axioms_strict UND.Chart.V_col_const
#print axioms UND.Chart.filter_of_black
#audit_axioms_strict UND.Chart.filter_of_black
#print axioms UND.Chart.exists_prank
#audit_axioms_strict UND.Chart.exists_prank
#print axioms UND.Chart.cutoff_of_dtiling
#audit_axioms_strict UND.Chart.cutoff_of_dtiling
#print axioms UND.Chart.cutoff_exists
#audit_axioms_strict UND.Chart.cutoff_exists
#print axioms UND.Chart.exists_qphase_shift
#audit_axioms_strict UND.Chart.exists_qphase_shift
#print axioms UND.Chart.wordAt_shift
#audit_axioms_strict UND.Chart.wordAt_shift
#print axioms UND.Chart.phaseTable_wordAt
#audit_axioms_strict UND.Chart.phaseTable_wordAt
#print axioms UND.Chart.phaseTable_wordAt_eq_lanePhase
#audit_axioms_strict UND.Chart.phaseTable_wordAt_eq_lanePhase
#print axioms UND.Chart.phaseTable_wordAt_eq_zero_iff
#audit_axioms_strict UND.Chart.phaseTable_wordAt_eq_zero_iff
#print axioms UND.Chart.phaseTable_wordAt_add_e1
#audit_axioms_strict UND.Chart.phaseTable_wordAt_add_e1
#print axioms UND.Chart.phaseTable_wordAt_add_e2
#audit_axioms_strict UND.Chart.phaseTable_wordAt_add_e2
#print axioms UND.prop_2_1_theCAOf
#audit_axioms_strict UND.prop_2_1_theCAOf
#print axioms UND.theoremA_of_theCA
#audit_axioms_strict UND.theoremA_of_theCA
#print axioms UND.Chart.IsRChart.tileE
#audit_axioms_strict UND.Chart.IsRChart.tileE
#print axioms UND.Chart.IsRChart.tileN
#audit_axioms_strict UND.Chart.IsRChart.tileN
#print axioms UND.Chart.IsRChart.matchE
#audit_axioms_strict UND.Chart.IsRChart.matchE
#print axioms UND.Chart.IsRChart.matchN
#audit_axioms_strict UND.Chart.IsRChart.matchN
#print axioms UND.Chart.IsRChart.isDTiling
#audit_axioms_strict UND.Chart.IsRChart.isDTiling
#print axioms UND.Chart.IsRChart.isQTiling
#audit_axioms_strict UND.Chart.IsRChart.isQTiling
#print axioms UND.Chart.IsRChart.mem_box_iff
#audit_axioms_strict UND.Chart.IsRChart.mem_box_iff
#print axioms UND.Chart.IsRChart.word_apply
#audit_axioms_strict UND.Chart.IsRChart.word_apply
#print axioms UND.Chart.IsRChart.word_eq
#audit_axioms_strict UND.Chart.IsRChart.word_eq
#print axioms UND.Chart.IsRChart.phase_eq
#audit_axioms_strict UND.Chart.IsRChart.phase_eq
#print axioms UND.Chart.IsRChart.phase_eq_zero_iff
#audit_axioms_strict UND.Chart.IsRChart.phase_eq_zero_iff
#print axioms UND.Chart.IsRChart.gate_iff
#audit_axioms_strict UND.Chart.IsRChart.gate_iff
#print axioms UND.Chart.strip_orient
#audit_axioms_strict UND.Chart.strip_orient
#print axioms UND.Chart.endpoint_lt_of_interior
#audit_axioms_strict UND.Chart.endpoint_lt_of_interior
#print axioms UND.Chart.inFrame_of_isFree
#audit_axioms_strict UND.Chart.inFrame_of_isFree
#print axioms UND.Chart.board_row_walls
#audit_axioms_strict UND.Chart.board_row_walls
#print axioms UND.Chart.board_col_walls
#audit_axioms_strict UND.Chart.board_col_walls
#print axioms UND.Chart.board_row
#audit_axioms_strict UND.Chart.board_row
#print axioms UND.Chart.board_col
#audit_axioms_strict UND.Chart.board_col
#print axioms UND.Chart.board_active
#audit_axioms_strict UND.Chart.board_active
#print axioms UND.Chart.exists_gap
#audit_axioms_strict UND.Chart.exists_gap
#print axioms UND.Chart.laminar_gap
#audit_axioms_strict UND.Chart.laminar_gap
#print axioms UND.Chart.map_BT_side_eq_some
#audit_axioms_strict UND.Chart.map_BT_side_eq_some
#print axioms UND.Chart.map_LR_side_eq_some
#audit_axioms_strict UND.Chart.map_LR_side_eq_some
#print axioms UND.Chart.toBT_injective
#audit_axioms_strict UND.Chart.toBT_injective
#print axioms UND.Chart.toLR_injective
#audit_axioms_strict UND.Chart.toLR_injective
#print axioms UND.Chart.board_not_vcarrier
#audit_axioms_strict UND.Chart.board_not_vcarrier
#print axioms UND.Chart.board_not_hcarrier
#audit_axioms_strict UND.Chart.board_not_hcarrier
#print axioms UND.Chart.flag_first
#audit_axioms_strict UND.Chart.flag_first
#print axioms UND.Chart.flag_second
#audit_axioms_strict UND.Chart.flag_second
#print axioms UND.Chart.fW_of_map
#audit_axioms_strict UND.Chart.fW_of_map
#print axioms UND.Chart.fE_of_map
#audit_axioms_strict UND.Chart.fE_of_map
#print axioms UND.Chart.fS_of_map
#audit_axioms_strict UND.Chart.fS_of_map
#print axioms UND.Chart.fN_of_map
#audit_axioms_strict UND.Chart.fN_of_map
#print axioms UND.Chart.decide_ite_wall
#audit_axioms_strict UND.Chart.decide_ite_wall
#print axioms UND.Chart.one_lt_ell_frame
#audit_axioms_strict UND.Chart.one_lt_ell_frame
#print axioms UND.Chart.board_flags_row
#audit_axioms_strict UND.Chart.board_flags_row
#print axioms UND.Chart.board_flags_col
#audit_axioms_strict UND.Chart.board_flags_col
#print axioms UND.Chart.channel
#audit_axioms_strict UND.Chart.channel
#print axioms UND.Chart.board_hchannel
#audit_axioms_strict UND.Chart.board_hchannel
#print axioms UND.Chart.board_vchannel
#audit_axioms_strict UND.Chart.board_vchannel
#print axioms UND.Chart.board_record
#audit_axioms_strict UND.Chart.board_record
#print axioms UND.Chart.board_tab
#audit_axioms_strict UND.Chart.board_tab
#print axioms UND.Chart.board_init
#audit_axioms_strict UND.Chart.board_init
#print axioms UND.Chart.board_step
#audit_axioms_strict UND.Chart.board_step
#print axioms UND.Chart.board_vlink
#audit_axioms_strict UND.Chart.board_vlink
#print axioms UND.Chart.board_bottom
#audit_axioms_strict UND.Chart.board_bottom
#print axioms UND.Chart.board_top
#audit_axioms_strict UND.Chart.board_top
#print axioms UND.Chart.prank_of_half
#audit_axioms_strict UND.Chart.prank_of_half
#print axioms UND.Chart.rfree_sub
#audit_axioms_strict UND.Chart.rfree_sub
#print axioms UND.Chart.two_pow_succ_le
#audit_axioms_strict UND.Chart.two_pow_succ_le
#print axioms UND.Chart.four_pow_eq_two_pow_mul
#audit_axioms_strict UND.Chart.four_pow_eq_two_pow_mul
#print axioms UND.Chart.add_two_le_of_two_pow
#audit_axioms_strict UND.Chart.add_two_le_of_two_pow
#print axioms UND.Chart.four_pow_split
#audit_axioms_strict UND.Chart.four_pow_split
#print axioms UND.Chart.prank_left
#audit_axioms_strict UND.Chart.prank_left
#print axioms UND.Chart.prank_center
#audit_axioms_strict UND.Chart.prank_center
#print axioms UND.Chart.prank_right
#audit_axioms_strict UND.Chart.prank_right
#print axioms UND.Chart.mod_of_odd_block
#audit_axioms_strict UND.Chart.mod_of_odd_block
#print axioms UND.Chart.not_isFree_of_mod
#audit_axioms_strict UND.Chart.not_isFree_of_mod
#print axioms UND.Chart.free_left_rank
#audit_axioms_strict UND.Chart.free_left_rank
#print axioms UND.Chart.free_right_rank
#audit_axioms_strict UND.Chart.free_right_rank
#print axioms UND.Chart.exists_two_pow_mul_odd
#audit_axioms_strict UND.Chart.exists_two_pow_mul_odd
#print axioms UND.Chart.lt_of_isFree
#audit_axioms_strict UND.Chart.lt_of_isFree
#print axioms UND.Chart.free_rank_even
#audit_axioms_strict UND.Chart.free_rank_even
#print axioms UND.Chart.allowed_lift
#audit_axioms_strict UND.Chart.allowed_lift
#print axioms UND.Chart.allowed_four_pow
#audit_axioms_strict UND.Chart.allowed_four_pow
#print axioms UND.Chart.initial_zero
#audit_axioms_strict UND.Chart.initial_zero
#print axioms UND.Chart.count_initial_zero
#audit_axioms_strict UND.Chart.count_initial_zero
#print axioms UND.Chart.chi2_eq
#audit_axioms_strict UND.Chart.chi2_eq
#print axioms UND.Chart.cutoff_of_flags
#audit_axioms_strict UND.Chart.cutoff_of_flags
#print axioms UND.Chart.input_read_large
#audit_axioms_strict UND.Chart.input_read_large
#print axioms UND.Chart.input_read_small
#audit_axioms_strict UND.Chart.input_read_small
#print axioms UND.MachineP.nextRow_up
#audit_axioms_strict UND.MachineP.nextRow_up
#print axioms UND.MachineP.nextRow_stay
#audit_axioms_strict UND.MachineP.nextRow_stay
#print axioms UND.MachineP.nextRow_down
#audit_axioms_strict UND.MachineP.nextRow_down
#print axioms UND.MachineP.nextRow_up_fail
#audit_axioms_strict UND.MachineP.nextRow_up_fail
#print axioms UND.MachineP.nextRow_down_fail
#audit_axioms_strict UND.MachineP.nextRow_down_fail
#print axioms UND.MachineP.colOf_eq
#audit_axioms_strict UND.MachineP.colOf_eq
#print axioms UND.MachineP.update_restrict
#audit_axioms_strict UND.MachineP.update_restrict
#print axioms UND.MachineP.nextRow_colOf
#audit_axioms_strict UND.MachineP.nextRow_colOf
#print axioms UND.MachineP.nextRow_iterate
#audit_axioms_strict UND.MachineP.nextRow_iterate
#print axioms UND.MachineP.runP_eq
#audit_axioms_strict UND.MachineP.runP_eq
#print axioms UND.MachineP.deltaP_fail
#audit_axioms_strict UND.MachineP.deltaP_fail
#print axioms UND.MachineP.deltaP_halt
#audit_axioms_strict UND.MachineP.deltaP_halt
#print axioms UND.MachineP.stepU_fail
#audit_axioms_strict UND.MachineP.stepU_fail
#print axioms UND.MachineP.stepU_iterate_fail
#audit_axioms_strict UND.MachineP.stepU_iterate_fail
#print axioms UND.MachineP.stepB_fail
#audit_axioms_strict UND.MachineP.stepB_fail
#print axioms UND.MachineP.stepU_halt
#audit_axioms_strict UND.MachineP.stepU_halt
#print axioms UND.MachineP.stepB_iterate
#audit_axioms_strict UND.MachineP.stepB_iterate
#print axioms UND.MachineP.stepB_iterate_eq
#audit_axioms_strict UND.MachineP.stepB_iterate_eq
#print axioms UND.MachineP.stepU_up
#audit_axioms_strict UND.MachineP.stepU_up
#print axioms UND.MachineP.stepU_stay
#audit_axioms_strict UND.MachineP.stepU_stay
#print axioms UND.MachineP.stepU_down
#audit_axioms_strict UND.MachineP.stepU_down
#print axioms UND.MachineP.stepU_down_zero
#audit_axioms_strict UND.MachineP.stepU_down_zero
#print axioms UND.MachineP.head_stepU_le
#audit_axioms_strict UND.MachineP.head_stepU_le
#print axioms UND.MachineP.head_iterate_le
#audit_axioms_strict UND.MachineP.head_iterate_le
#print axioms UND.MachineP.Reaches.refl
#audit_axioms_strict UND.MachineP.Reaches.refl
#print axioms UND.MachineP.Reaches.trans
#audit_axioms_strict UND.MachineP.Reaches.trans
#print axioms UND.MachineP.Reaches.of_iterate
#audit_axioms_strict UND.MachineP.Reaches.of_iterate
#print axioms UND.MachineP.Reaches.step
#audit_axioms_strict UND.MachineP.Reaches.step
#print axioms UND.MachineP.move_up
#audit_axioms_strict UND.MachineP.move_up
#print axioms UND.MachineP.move_down
#audit_axioms_strict UND.MachineP.move_down
#print axioms UND.MachineP.scan_up
#audit_axioms_strict UND.MachineP.scan_up
#print axioms UND.MachineP.deltaP_ret_z
#audit_axioms_strict UND.MachineP.deltaP_ret_z
#print axioms UND.MachineP.deltaP_ret
#audit_axioms_strict UND.MachineP.deltaP_ret
#print axioms UND.MachineP.ret_home
#audit_axioms_strict UND.MachineP.ret_home
#print axioms UND.MachineP.stepU_state_halt
#audit_axioms_strict UND.MachineP.stepU_state_halt
#print axioms UND.MachineP.stepU_state_fail
#audit_axioms_strict UND.MachineP.stepU_state_fail
#print axioms UND.MachineP.iterate_halt
#audit_axioms_strict UND.MachineP.iterate_halt
#print axioms UND.MachineP.iterate_fail
#audit_axioms_strict UND.MachineP.iterate_fail
#print axioms UND.MachineP.not_halt_before
#audit_axioms_strict UND.MachineP.not_halt_before
#print axioms UND.MachineP.fail_after
#audit_axioms_strict UND.MachineP.fail_after
#print axioms UND.MachineP.never_halt_of_fail
#audit_axioms_strict UND.MachineP.never_halt_of_fail
#print axioms UND.MachineP.program_forget
#audit_axioms_strict UND.MachineP.program_forget
#print axioms UND.MachineP.deltaP_forget
#audit_axioms_strict UND.MachineP.deltaP_forget
#print axioms UND.MachineP.deltaP_ne_scan
#audit_axioms_strict UND.MachineP.deltaP_ne_scan
#print axioms UND.MachineP.stepU_ne_scan
#audit_axioms_strict UND.MachineP.stepU_ne_scan
#print axioms UND.MachineP.update_forget
#audit_axioms_strict UND.MachineP.update_forget
#print axioms UND.MachineP.stepU_forget
#audit_axioms_strict UND.MachineP.stepU_forget
#print axioms UND.MachineP.iterate_forget
#audit_axioms_strict UND.MachineP.iterate_forget
#print axioms UND.MachineP.state_iterate_forget
#audit_axioms_strict UND.MachineP.state_iterate_forget
#print axioms UND.MachineP.deltaP_scan_one
#audit_axioms_strict UND.MachineP.deltaP_scan_one
#print axioms UND.MachineP.deltaP_scan_plus
#audit_axioms_strict UND.MachineP.deltaP_scan_plus
#print axioms UND.MachineP.deltaP_scan_fail
#audit_axioms_strict UND.MachineP.deltaP_scan_fail
#print axioms UND.MachineP.scan_phase
#audit_axioms_strict UND.MachineP.scan_phase
#print axioms UND.MachineP.scan_plus
#audit_axioms_strict UND.MachineP.scan_plus
#print axioms UND.MachineP.scan_guard
#audit_axioms_strict UND.MachineP.scan_guard
#print axioms UND.MachineP.scan_forever
#audit_axioms_strict UND.MachineP.scan_forever
#print axioms UND.MachineP.wt_z
#audit_axioms_strict UND.MachineP.wt_z
#print axioms UND.MachineP.update_wt_u
#audit_axioms_strict UND.MachineP.update_wt_u
#print axioms UND.MachineP.deltaP_run
#audit_axioms_strict UND.MachineP.deltaP_run
#print axioms UND.MachineP.sim_step
#audit_axioms_strict UND.MachineP.sim_step
#print axioms UND.MachineP.sim_step_none
#audit_axioms_strict UND.MachineP.sim_step_none
#print axioms UND.MachineP.run_succ
#audit_axioms_strict UND.MachineP.run_succ
#print axioms UND.MachineP.sim_inv
#audit_axioms_strict UND.MachineP.sim_inv
#print axioms UND.MachineP.sim_halts
#audit_axioms_strict UND.MachineP.sim_halts
#print axioms UND.MachineP.sim_no_halt
#audit_axioms_strict UND.MachineP.sim_no_halt
#print axioms UND.MachineP.deltaP_plus
#audit_axioms_strict UND.MachineP.deltaP_plus
#print axioms UND.MachineP.deltaP_setend
#audit_axioms_strict UND.MachineP.deltaP_setend
#print axioms UND.MachineP.deltaP_r_skip
#audit_axioms_strict UND.MachineP.deltaP_r_skip
#print axioms UND.MachineP.deltaP_r_mark
#audit_axioms_strict UND.MachineP.deltaP_r_mark
#print axioms UND.MachineP.deltaP_r_even
#audit_axioms_strict UND.MachineP.deltaP_r_even
#print axioms UND.MachineP.deltaP_r_one
#audit_axioms_strict UND.MachineP.deltaP_r_one
#print axioms UND.MachineP.deltaP_appendN_one
#audit_axioms_strict UND.MachineP.deltaP_appendN_one
#print axioms UND.MachineP.deltaP_appendN_zero
#audit_axioms_strict UND.MachineP.deltaP_appendN_zero
#print axioms UND.MachineP.deltaP_skip_lt
#audit_axioms_strict UND.MachineP.deltaP_skip_lt
#print axioms UND.MachineP.deltaP_skip_last
#audit_axioms_strict UND.MachineP.deltaP_skip_last
#print axioms UND.MachineP.deltaP_findN_two
#audit_axioms_strict UND.MachineP.deltaP_findN_two
#print axioms UND.MachineP.deltaP_findN_one
#audit_axioms_strict UND.MachineP.deltaP_findN_one
#print axioms UND.MachineP.deltaP_findN_zero
#audit_axioms_strict UND.MachineP.deltaP_findN_zero
#print axioms UND.MachineP.deltaP_appendU_one
#audit_axioms_strict UND.MachineP.deltaP_appendU_one
#print axioms UND.MachineP.deltaP_appendU_zero
#audit_axioms_strict UND.MachineP.deltaP_appendU_zero
#print axioms UND.MachineP.update_wt_p
#audit_axioms_strict UND.MachineP.update_wt_p
#print axioms UND.MachineP.update_wt_n
#audit_axioms_strict UND.MachineP.update_wt_n
#print axioms UND.MachineP.reach_up
#audit_axioms_strict UND.MachineP.reach_up
#print axioms UND.MachineP.ret_home_wt
#audit_axioms_strict UND.MachineP.ret_home_wt
#print axioms UND.MachineP.forget_tape1
#audit_axioms_strict UND.MachineP.forget_tape1
#print axioms UND.MachineP.plus_phase
#audit_axioms_strict UND.MachineP.plus_phase
#print axioms UND.MachineP.pass_block
#audit_axioms_strict UND.MachineP.pass_block
#print axioms UND.MachineP.not_dvd_between
#audit_axioms_strict UND.MachineP.not_dvd_between
#print axioms UND.MachineP.passP_succ
#audit_axioms_strict UND.MachineP.passP_succ
#print axioms UND.MachineP.pass_blocks
#audit_axioms_strict UND.MachineP.pass_blocks
#print axioms UND.MachineP.passP_end
#audit_axioms_strict UND.MachineP.passP_end
#print axioms UND.MachineP.two_pow_split
#audit_axioms_strict UND.MachineP.two_pow_split
#print axioms UND.MachineP.halving_step
#audit_axioms_strict UND.MachineP.halving_step
#print axioms UND.MachineP.halving_all
#audit_axioms_strict UND.MachineP.halving_all
#print axioms UND.MachineP.halving_last
#audit_axioms_strict UND.MachineP.halving_last
#print axioms UND.MachineP.skip_loop
#audit_axioms_strict UND.MachineP.skip_loop
#print axioms UND.MachineP.skip_phase
#audit_axioms_strict UND.MachineP.skip_phase
#print axioms UND.MachineP.update_wt_u'
#audit_axioms_strict UND.MachineP.update_wt_u'
#print axioms UND.MachineP.zero_ne_one_sym
#audit_axioms_strict UND.MachineP.zero_ne_one_sym
#print axioms UND.MachineP.copy_step
#audit_axioms_strict UND.MachineP.copy_step
#print axioms UND.MachineP.copy_all
#audit_axioms_strict UND.MachineP.copy_all
#print axioms UND.MachineP.copy_last
#audit_axioms_strict UND.MachineP.copy_last
#print axioms UND.MachineP.fnTok_last
#audit_axioms_strict UND.MachineP.fnTok_last
#print axioms UND.MachineP.uTape_eq_start
#audit_axioms_strict UND.MachineP.uTape_eq_start
#print axioms UND.MachineP.reaches_run
#audit_axioms_strict UND.MachineP.reaches_run
#print axioms UND.MachineP.forgetC_tape1
#audit_axioms_strict UND.MachineP.forgetC_tape1
#print axioms UND.MachineP.forget_scan
#audit_axioms_strict UND.MachineP.forget_scan
#print axioms UND.MachineP.decode_halts
#audit_axioms_strict UND.MachineP.decode_halts
#print axioms UND.MachineP.decode_no_halt
#audit_axioms_strict UND.MachineP.decode_no_halt
#print axioms UND.MachineP.guard_no_halt
#audit_axioms_strict UND.MachineP.guard_no_halt
#print axioms UND.MachineP.runP_no_halt
#audit_axioms_strict UND.MachineP.runP_no_halt
#print axioms UND.MachineP.runP_halts
#audit_axioms_strict UND.MachineP.runP_halts
#print axioms UND.Chart.freeOff_finite
#audit_axioms_strict UND.Chart.freeOff_finite
#print axioms UND.Chart.count_freeOff
#audit_axioms_strict UND.Chart.count_freeOff
#print axioms UND.Chart.card_freeOff
#audit_axioms_strict UND.Chart.card_freeOff
#print axioms UND.Chart.freeOff_nth
#audit_axioms_strict UND.Chart.freeOff_nth
#print axioms UND.Chart.freeAt_free
#audit_axioms_strict UND.Chart.freeAt_free
#print axioms UND.Chart.freeOff_zero
#audit_axioms_strict UND.Chart.freeOff_zero
#print axioms UND.Chart.nth_freeOff_zero
#audit_axioms_strict UND.Chart.nth_freeOff_zero
#print axioms UND.Chart.freeAt_zero
#audit_axioms_strict UND.Chart.freeAt_zero
#print axioms UND.Chart.freeAt_lt
#audit_axioms_strict UND.Chart.freeAt_lt
#print axioms UND.Chart.freeAt_eq_zero_iff
#audit_axioms_strict UND.Chart.freeAt_eq_zero_iff
#print axioms UND.Chart.freeAt_consec
#audit_axioms_strict UND.Chart.freeAt_consec
#print axioms UND.Chart.freeAt_last
#audit_axioms_strict UND.Chart.freeAt_last
#print axioms UND.Chart.board_run
#audit_axioms_strict UND.Chart.board_run
#print axioms UND.Chart.prank_frameLo
#audit_axioms_strict UND.Chart.prank_frameLo
#print axioms UND.Chart.isEnd_of_bottomEnd
#audit_axioms_strict UND.Chart.isEnd_of_bottomEnd
#print axioms UND.Chart.bottomEnd_gate
#audit_axioms_strict UND.Chart.bottomEnd_gate
#print axioms UND.Chart.chart_wrong_flag
#audit_axioms_strict UND.Chart.chart_wrong_flag
#print axioms UND.MachineP.program_tracks
#audit_axioms_strict UND.MachineP.program_tracks
#print axioms UND.MachineP.deltaP_tracks
#audit_axioms_strict UND.MachineP.deltaP_tracks
#print axioms UND.MachineP.update_tracks
#audit_axioms_strict UND.MachineP.update_tracks
#print axioms UND.MachineP.stepB_tracks
#audit_axioms_strict UND.MachineP.stepB_tracks
#print axioms UND.MachineP.runP_tracks
#audit_axioms_strict UND.MachineP.runP_tracks
#print axioms UND.Chart.prankOf_spec
#audit_axioms_strict UND.Chart.prankOf_spec
#print axioms UND.Chart.prankOf_eq
#audit_axioms_strict UND.Chart.prankOf_eq
#print axioms UND.Chart.board_no_halt
#audit_axioms_strict UND.Chart.board_no_halt
#print axioms UND.Chart.board_run_no_halt
#audit_axioms_strict UND.Chart.board_run_no_halt
#print axioms UND.Chart.nd_eq
#audit_axioms_strict UND.Chart.nd_eq
#print axioms UND.Chart.freeAt_eq_zeta
#audit_axioms_strict UND.Chart.freeAt_eq_zeta
#print axioms UND.Chart.rankOK_okBits
#audit_axioms_strict UND.Chart.rankOK_okBits
#print axioms UND.Chart.dqOf_toQ
#audit_axioms_strict UND.Chart.dqOf_toQ
#print axioms UND.Chart.exists_prank_of_notInt
#audit_axioms_strict UND.Chart.exists_prank_of_notInt
#print axioms UND.Chart.dqOf_spec
#audit_axioms_strict UND.Chart.dqOf_spec
#print axioms UND.Chart.HSegM.hseg
#audit_axioms_strict UND.Chart.HSegM.hseg
#print axioms UND.Chart.VSegM.vseg
#audit_axioms_strict UND.Chart.VSegM.vseg
#print axioms UND.Chart.GPosM.gpos
#audit_axioms_strict UND.Chart.GPosM.gpos
#print axioms UND.Chart.HSegM_unique
#audit_axioms_strict UND.Chart.HSegM_unique
#print axioms UND.Chart.VSegM_unique
#audit_axioms_strict UND.Chart.VSegM_unique
#print axioms UND.Chart.GPosM_unique
#audit_axioms_strict UND.Chart.GPosM_unique
#print axioms UND.Chart.lEm_of
#audit_axioms_strict UND.Chart.lEm_of
#print axioms UND.Chart.lEm_none
#audit_axioms_strict UND.Chart.lEm_none
#print axioms UND.Chart.lNm_of
#audit_axioms_strict UND.Chart.lNm_of
#print axioms UND.Chart.lNm_none
#audit_axioms_strict UND.Chart.lNm_none
#print axioms UND.Chart.kFm_of
#audit_axioms_strict UND.Chart.kFm_of
#print axioms UND.Chart.kFm_none
#audit_axioms_strict UND.Chart.kFm_none
#print axioms UND.Chart.sAt_zero
#audit_axioms_strict UND.Chart.sAt_zero
#print axioms UND.Chart.sAt_of
#audit_axioms_strict UND.Chart.sAt_of
#print axioms UND.Chart.runP_succ
#audit_axioms_strict UND.Chart.runP_succ
#print axioms UND.Chart.sAt_succ
#audit_axioms_strict UND.Chart.sAt_succ
#print axioms UND.Chart.lEm_gsite
#audit_axioms_strict UND.Chart.lEm_gsite
#print axioms UND.Chart.lWm_gsite
#audit_axioms_strict UND.Chart.lWm_gsite
#print axioms UND.Chart.lNm_gsite
#audit_axioms_strict UND.Chart.lNm_gsite
#print axioms UND.Chart.lSm_gsite
#audit_axioms_strict UND.Chart.lSm_gsite
#print axioms UND.Chart.kFm_gsite
#audit_axioms_strict UND.Chart.kFm_gsite
#print axioms UND.Chart.raw_active
#audit_axioms_strict UND.Chart.raw_active
#print axioms UND.Chart.raw_O1
#audit_axioms_strict UND.Chart.raw_O1
#print axioms UND.Chart.raw_O2
#audit_axioms_strict UND.Chart.raw_O2
#print axioms UND.Chart.raw_E1
#audit_axioms_strict UND.Chart.raw_E1
#print axioms UND.Chart.raw_E2
#audit_axioms_strict UND.Chart.raw_E2
#print axioms UND.Chart.raw_E3
#audit_axioms_strict UND.Chart.raw_E3
#print axioms UND.Chart.raw_K1
#audit_axioms_strict UND.Chart.raw_K1
#print axioms UND.Chart.raw_K2
#audit_axioms_strict UND.Chart.raw_K2
#print axioms UND.Chart.raw_H
#audit_axioms_strict UND.Chart.raw_H
#print axioms UND.Chart.raw_B
#audit_axioms_strict UND.Chart.raw_B
#print axioms UND.Chart.raw_rules
#audit_axioms_strict UND.Chart.raw_rules
#print axioms UND.Chart.raw_K3
#audit_axioms_strict UND.Chart.raw_K3
#print axioms UND.Chart.raw_allowed
#audit_axioms_strict UND.Chart.raw_allowed
#print axioms UND.Chart.raw_tileOK
#audit_axioms_strict UND.Chart.raw_tileOK
#print axioms UND.Chart.raw_matchE
#audit_axioms_strict UND.Chart.raw_matchE
#print axioms UND.Chart.raw_matchN
#audit_axioms_strict UND.Chart.raw_matchN
#print axioms UND.Chart.raw_tileE
#audit_axioms_strict UND.Chart.raw_tileE
#print axioms UND.Chart.raw_tileN
#audit_axioms_strict UND.Chart.raw_tileN
#print axioms UND.Chart.chartOf_val
#audit_axioms_strict UND.Chart.chartOf_val
#print axioms UND.Chart.chartOf_isRChart
#audit_axioms_strict UND.Chart.chartOf_isRChart
#print axioms UND.Chart.chartOf_quarters
#audit_axioms_strict UND.Chart.chartOf_quarters
#print axioms UND.Chart.chartOf_phase
#audit_axioms_strict UND.Chart.chartOf_phase
#print axioms UND.Chart.chartOf_V
#audit_axioms_strict UND.Chart.chartOf_V
#print axioms UND.Chart.chartOf_H
#audit_axioms_strict UND.Chart.chartOf_H
#print axioms UND.Chart.chartOf_bottom_flag
#audit_axioms_strict UND.Chart.chartOf_bottom_flag
#print axioms UND.Chart.dig_shift
#audit_axioms_strict UND.Chart.dig_shift
#print axioms UND.Chart.prank_iff_dig
#audit_axioms_strict UND.Chart.prank_iff_dig
#print axioms UND.Chart.prank_shift
#audit_axioms_strict UND.Chart.prank_shift
#print axioms UND.Chart.prankOf_congr
#audit_axioms_strict UND.Chart.prankOf_congr
#print axioms UND.Chart.prankOf_shift
#audit_axioms_strict UND.Chart.prankOf_shift
#print axioms UND.Chart.fshift_phase
#audit_axioms_strict UND.Chart.fshift_phase
#print axioms UND.Chart.fq_spec
#audit_axioms_strict UND.Chart.fq_spec
#print axioms UND.Chart.frameLo_shift
#audit_axioms_strict UND.Chart.frameLo_shift
#print axioms UND.Chart.frameHi_shift
#audit_axioms_strict UND.Chart.frameHi_shift
#print axioms UND.Chart.inFrame_shift
#audit_axioms_strict UND.Chart.inFrame_shift
#print axioms UND.Chart.isFree_shift
#audit_axioms_strict UND.Chart.isFree_shift
#print axioms UND.Chart.zeta_shift
#audit_axioms_strict UND.Chart.zeta_shift
#print axioms UND.Chart.pshift_addDig
#audit_axioms_strict UND.Chart.pshift_addDig
#print axioms UND.Chart.PShift.fcol
#audit_axioms_strict UND.Chart.PShift.fcol
#print axioms UND.Chart.PShift.frow
#audit_axioms_strict UND.Chart.PShift.frow
#print axioms UND.Chart.PShift.zeta1
#audit_axioms_strict UND.Chart.PShift.zeta1
#print axioms UND.Chart.PShift.zeta2
#audit_axioms_strict UND.Chart.PShift.zeta2
#print axioms UND.Chart.PShift.prank1
#audit_axioms_strict UND.Chart.PShift.prank1
#print axioms UND.Chart.PShift.prank2
#audit_axioms_strict UND.Chart.PShift.prank2
#print axioms UND.Chart.PShift.cutH_eq
#audit_axioms_strict UND.Chart.PShift.cutH_eq
#print axioms UND.Chart.PShift.cutPi_eq
#audit_axioms_strict UND.Chart.PShift.cutPi_eq
#print axioms UND.Chart.runP_congr
#audit_axioms_strict UND.Chart.runP_congr
#print axioms UND.Chart.PShift.sAt_eq
#audit_axioms_strict UND.Chart.PShift.sAt_eq
#print axioms UND.Chart.wdL_shift
#audit_axioms_strict UND.Chart.wdL_shift
#print axioms UND.Chart.wdR_shift
#audit_axioms_strict UND.Chart.wdR_shift
#print axioms UND.Chart.wtag_shift
#audit_axioms_strict UND.Chart.wtag_shift
#print axioms UND.Chart.evTag_shift
#audit_axioms_strict UND.Chart.evTag_shift
#print axioms UND.Chart.ptrans_addDig
#audit_axioms_strict UND.Chart.ptrans_addDig
#print axioms UND.Chart.PTrans.rowW
#audit_axioms_strict UND.Chart.PTrans.rowW
#print axioms UND.Chart.PTrans.colW
#audit_axioms_strict UND.Chart.PTrans.colW
#print axioms UND.Chart.PTrans.oEc
#audit_axioms_strict UND.Chart.PTrans.oEc
#print axioms UND.Chart.PTrans.oNc
#audit_axioms_strict UND.Chart.PTrans.oNc
#print axioms UND.Chart.PTrans.actF
#audit_axioms_strict UND.Chart.PTrans.actF
#print axioms UND.Chart.PTrans.eEc
#audit_axioms_strict UND.Chart.PTrans.eEc
#print axioms UND.Chart.PTrans.eNc
#audit_axioms_strict UND.Chart.PTrans.eNc
#print axioms UND.Chart.PTrans.dqOf
#audit_axioms_strict UND.Chart.PTrans.dqOf
#print axioms UND.Chart.PTrans.hseg
#audit_axioms_strict UND.Chart.PTrans.hseg
#print axioms UND.Chart.PTrans.vseg
#audit_axioms_strict UND.Chart.PTrans.vseg
#print axioms UND.Chart.PTrans.gsite
#audit_axioms_strict UND.Chart.PTrans.gsite
#print axioms UND.Chart.PTrans.gpos
#audit_axioms_strict UND.Chart.PTrans.gpos
#print axioms UND.Chart.PTrans.lEm
#audit_axioms_strict UND.Chart.PTrans.lEm
#print axioms UND.Chart.PTrans.lNm
#audit_axioms_strict UND.Chart.PTrans.lNm
#print axioms UND.Chart.PTrans.kFm
#audit_axioms_strict UND.Chart.PTrans.kFm
#print axioms UND.Chart.PTrans.rawVal
#audit_axioms_strict UND.Chart.PTrans.rawVal
#print axioms UND.Chart.PTrans.wordAt
#audit_axioms_strict UND.Chart.PTrans.wordAt
#print axioms UND.Chart.PTrans.rawOf
#audit_axioms_strict UND.Chart.PTrans.rawOf
#print axioms UND.Chart.PTrans.chartOf
#audit_axioms_strict UND.Chart.PTrans.chartOf
#print axioms UND.Chart.chartOf_shift
#audit_axioms_strict UND.Chart.chartOf_shift
#print axioms UND.Chart.measurableSet_dig_col
#audit_axioms_strict UND.Chart.measurableSet_dig_col
#print axioms UND.Chart.measurableSet_dig_row
#audit_axioms_strict UND.Chart.measurableSet_dig_row
#print axioms UND.Chart.measurableSet_digP
#audit_axioms_strict UND.Chart.measurableSet_digP
#print axioms UND.Chart.measurableSet_resolving
#audit_axioms_strict UND.Chart.measurableSet_resolving
#print axioms UND.Chart.measurableSet_typical
#audit_axioms_strict UND.Chart.measurableSet_typical
#print axioms UND.Chart.haar_typical
#audit_axioms_strict UND.Chart.haar_typical
#print axioms UND.Chart.mlevel_pi
#audit_axioms_strict UND.Chart.mlevel_pi
#print axioms UND.Chart.mlevel_choose'
#audit_axioms_strict UND.Chart.mlevel_choose'
#print axioms UND.Chart.mlevel_prankOf_col
#audit_axioms_strict UND.Chart.mlevel_prankOf_col
#print axioms UND.Chart.mlevel_prankOf_row
#audit_axioms_strict UND.Chart.mlevel_prankOf_row
#print axioms UND.Chart.mlevel_dqOf
#audit_axioms_strict UND.Chart.mlevel_dqOf
#print axioms UND.Chart.freeAt_congr
#audit_axioms_strict UND.Chart.freeAt_congr
#print axioms UND.Chart.mlevel_freeAt_row
#audit_axioms_strict UND.Chart.mlevel_freeAt_row
#print axioms UND.Chart.mlevel_cutH
#audit_axioms_strict UND.Chart.mlevel_cutH
#print axioms UND.Chart.mlevel_cutPi
#audit_axioms_strict UND.Chart.mlevel_cutPi
#print axioms UND.Chart.mlevel_sAt
#audit_axioms_strict UND.Chart.mlevel_sAt
#print axioms UND.Chart.measurableSet_HSegM
#audit_axioms_strict UND.Chart.measurableSet_HSegM
#print axioms UND.Chart.measurableSet_VSegM
#audit_axioms_strict UND.Chart.measurableSet_VSegM
#print axioms UND.Chart.measurableSet_GPosM
#audit_axioms_strict UND.Chart.measurableSet_GPosM
#print axioms UND.Chart.mlevel_lEm
#audit_axioms_strict UND.Chart.mlevel_lEm
#print axioms UND.Chart.mlevel_lNm
#audit_axioms_strict UND.Chart.mlevel_lNm
#print axioms UND.Chart.mlevel_kFm
#audit_axioms_strict UND.Chart.mlevel_kFm
#print axioms UND.Chart.mlevel_rawVal
#audit_axioms_strict UND.Chart.mlevel_rawVal
#print axioms UND.Chart.mlevel_rawOf
#audit_axioms_strict UND.Chart.mlevel_rawOf
#print axioms UND.Chart.measurable_chartOf
#audit_axioms_strict UND.Chart.measurable_chartOf
#print axioms UND.Chart.measurable_quartersOf
#audit_axioms_strict UND.Chart.measurable_quartersOf
#print axioms UND.Chart.isProbabilityMeasure_chartLaw
#audit_axioms_strict UND.Chart.isProbabilityMeasure_chartLaw
#print axioms UND.Chart.chartLaw_shift
#audit_axioms_strict UND.Chart.chartLaw_shift
#print axioms UND.Chart.measurableSet_goodChart
#audit_axioms_strict UND.Chart.measurableSet_goodChart
#print axioms UND.Chart.goodChart_chartOf
#audit_axioms_strict UND.Chart.goodChart_chartOf
#print axioms UND.Chart.ae_goodChart
#audit_axioms_strict UND.Chart.ae_goodChart
#print axioms UND.Chart.chart_law_exists
#audit_axioms_strict UND.Chart.chart_law_exists
#print axioms UND.Coh.card_PSrc
#audit_axioms_strict UND.Coh.card_PSrc
#print axioms UND.Coh.insertNth_inj
#audit_axioms_strict UND.Coh.insertNth_inj
#print axioms UND.Coh.pHi_injective
#audit_axioms_strict UND.Coh.pHi_injective
#print axioms UND.Coh.pLo_injective
#audit_axioms_strict UND.Coh.pLo_injective
#print axioms UND.Coh.provOff_pair
#audit_axioms_strict UND.Coh.provOff_pair
#print axioms UND.Coh.exists_pair
#audit_axioms_strict UND.Coh.exists_pair
#print axioms UND.Coh.sep_zero
#audit_axioms_strict UND.Coh.sep_zero
#print axioms UND.Coh.sep_step
#audit_axioms_strict UND.Coh.sep_step
#print axioms UND.Coh.UL.drvA
#audit_axioms_strict UND.Coh.UL.drvA
#print axioms UND.Coh.one_cluster
#audit_axioms_strict UND.Coh.one_cluster
#print axioms UND.Coh.card_cluster
#audit_axioms_strict UND.Coh.card_cluster
#print axioms UND.Coh.card_marked_le
#audit_axioms_strict UND.Coh.card_marked_le
#print axioms UND.Coh.card_failed_le
#audit_axioms_strict UND.Coh.card_failed_le
#print axioms UND.Coh.ul_of_good
#audit_axioms_strict UND.Coh.ul_of_good
#print axioms UND.Coh.coh_rel
#audit_axioms_strict UND.Coh.coh_rel
#print axioms UND.Coh.coherence_eq
#audit_axioms_strict UND.Coh.coherence_eq
#print axioms UND.Coh.coherence_compat
#audit_axioms_strict UND.Coh.coherence_compat
#print axioms UND.Coh.coh_back
#audit_axioms_strict UND.Coh.coh_back
#print axioms UND.Coh.coh_persist
#audit_axioms_strict UND.Coh.coh_persist
#print axioms UND.Coh.step_toward
#audit_axioms_strict UND.Coh.step_toward
#print axioms UND.Coh.coh_cover
#audit_axioms_strict UND.Coh.coh_cover
#print axioms UND.Coh.coherent_chart
#audit_axioms_strict UND.Coh.coherent_chart
#print axioms UND.Coh.markedAt_mono
#audit_axioms_strict UND.Coh.markedAt_mono
#print axioms UND.Coh.twoCl_mono
#audit_axioms_strict UND.Coh.twoCl_mono
#print axioms UND.Coh.markedFrom_mono
#audit_axioms_strict UND.Coh.markedFrom_mono
#print axioms UND.Coh.markedFrom_mono'
#audit_axioms_strict UND.Coh.markedFrom_mono'
#print axioms UND.Coh.marked_closed
#audit_axioms_strict UND.Coh.marked_closed
#print axioms UND.Coh.isFlagTraj_of_complete
#audit_axioms_strict UND.Coh.isFlagTraj_of_complete
#print axioms UND.Coh.coherence_complete
#audit_axioms_strict UND.Coh.coherence_complete
#print axioms UND.Raw.chi_par
#audit_axioms_strict UND.Raw.chi_par
#print axioms UND.Raw.par_time
#audit_axioms_strict UND.Raw.par_time
#print axioms UND.Raw.par_ne
#audit_axioms_strict UND.Raw.par_ne
#print axioms UND.Raw.card_box_one
#audit_axioms_strict UND.Raw.card_box_one
#print axioms UND.Raw.card_nbr_le
#audit_axioms_strict UND.Raw.card_nbr_le
#print axioms UND.Raw.par_mem_nbr
#audit_axioms_strict UND.Raw.par_mem_nbr
#print axioms UND.Raw.mem_nbr_par
#audit_axioms_strict UND.Raw.mem_nbr_par
#print axioms UND.Raw.inGraph_par
#audit_axioms_strict UND.Raw.inGraph_par
#print axioms UND.Raw.not_isDiag_par
#audit_axioms_strict UND.Raw.not_isDiag_par
#print axioms UND.Raw.MF.time_lt
#audit_axioms_strict UND.Raw.MF.time_lt
#print axioms UND.Raw.mf_par
#audit_axioms_strict UND.Raw.mf_par
#print axioms UND.Raw.exists_pgood
#audit_axioms_strict UND.Raw.exists_pgood
#print axioms UND.Raw.pd_spec
#audit_axioms_strict UND.Raw.pd_spec
#print axioms UND.Raw.sel_box
#audit_axioms_strict UND.Raw.sel_box
#print axioms UND.Raw.sel_mf
#audit_axioms_strict UND.Raw.sel_mf
#print axioms UND.Raw.sel_ne
#audit_axioms_strict UND.Raw.sel_ne
#print axioms UND.Raw.sys_sup
#audit_axioms_strict UND.Raw.sys_sup
#print axioms UND.Raw.sel_good
#audit_axioms_strict UND.Raw.sel_good
#print axioms UND.Raw.isBlockOffset_prov
#audit_axioms_strict UND.Raw.isBlockOffset_prov
#print axioms UND.Raw.psi_par
#audit_axioms_strict UND.Raw.psi_par
#print axioms UND.Raw.isPotential_psi
#audit_axioms_strict UND.Raw.isPotential_psi
#print axioms UND.Raw.mf_of_reach
#audit_axioms_strict UND.Raw.mf_of_reach
#print axioms UND.Raw.flag_of_term
#audit_axioms_strict UND.Raw.flag_of_term
#print axioms UND.Raw.gLen_eq_gBin
#audit_axioms_strict UND.Raw.gLen_eq_gBin
#print axioms UND.Raw.armEdge_spec
#audit_axioms_strict UND.Raw.armEdge_spec
#print axioms UND.Raw.exists_edge_of_reach
#audit_axioms_strict UND.Raw.exists_edge_of_reach
#print axioms UND.Raw.isContour_flag
#audit_axioms_strict UND.Raw.isContour_flag
#print axioms UND.Raw.exists_contour_nf
#audit_axioms_strict UND.Raw.exists_contour_nf
#print axioms UND.Raw.exists_contour
#audit_axioms_strict UND.Raw.exists_contour
#print axioms UND.Raw.card_pathEdges_le
#audit_axioms_strict UND.Raw.card_pathEdges_le
#print axioms UND.Raw.pathEdges_reach
#audit_axioms_strict UND.Raw.pathEdges_reach
#print axioms UND.Raw.pathEdges_connected
#audit_axioms_strict UND.Raw.pathEdges_connected
#print axioms UND.Raw.pathEdges_inGraph
#audit_axioms_strict UND.Raw.pathEdges_inGraph
#print axioms UND.Raw.connectedAt_union
#audit_axioms_strict UND.Raw.connectedAt_union
#print axioms UND.Raw.inGraph_union
#audit_axioms_strict UND.Raw.inGraph_union
#print axioms UND.Raw.exists_cover
#audit_axioms_strict UND.Raw.exists_cover
#print axioms UND.Raw.noiseLaw₂_flags_eq
#audit_axioms_strict UND.Raw.noiseLaw₂_flags_eq
#print axioms UND.Raw.flags_measure
#audit_axioms_strict UND.Raw.flags_measure
#print axioms UND.Raw.measure_le_tsum_from
#audit_axioms_strict UND.Raw.measure_le_tsum_from
#print axioms UND.Raw.pathEv_null
#audit_axioms_strict UND.Raw.pathEv_null
#print axioms UND.Raw.raw_paths
#audit_axioms_strict UND.Raw.raw_paths
#print axioms UND.Raw.raw_paths_threshold
#audit_axioms_strict UND.Raw.raw_paths_threshold
#print axioms UND.Deep.T_eq
#audit_axioms_strict UND.Deep.T_eq
#print axioms UND.Deep.exists_two_clusters
#audit_axioms_strict UND.Deep.exists_two_clusters
#print axioms UND.Deep.prop_of_mem_filter'
#audit_axioms_strict UND.Deep.prop_of_mem_filter'
#print axioms UND.Deep.chk_center
#audit_axioms_strict UND.Deep.chk_center
#print axioms UND.Deep.Ctx.depth_spec
#audit_axioms_strict UND.Deep.Ctx.depth_spec
#print axioms UND.Deep.Ctx.depth_le
#audit_axioms_strict UND.Deep.Ctx.depth_le
#print axioms UND.Deep.Ctx.exists_pgoodD_a
#audit_axioms_strict UND.Deep.Ctx.exists_pgoodD_a
#print axioms UND.Deep.Ctx.zero_mem_box
#audit_axioms_strict UND.Deep.Ctx.zero_mem_box
#print axioms UND.Deep.Ctx.exists_pgoodD_v
#audit_axioms_strict UND.Deep.Ctx.exists_pgoodD_v
#print axioms UND.Deep.Ctx.pdD_spec
#audit_axioms_strict UND.Deep.Ctx.pdD_spec
#print axioms UND.Deep.Ctx.childOK_sel
#audit_axioms_strict UND.Deep.Ctx.childOK_sel
#print axioms UND.Deep.Ctx.selD_ne
#audit_axioms_strict UND.Deep.Ctx.selD_ne
#print axioms UND.Deep.Ctx.rk_supD
#audit_axioms_strict UND.Deep.Ctx.rk_supD
#print axioms UND.Deep.Ctx.sysD_sup
#audit_axioms_strict UND.Deep.Ctx.sysD_sup
#print axioms UND.Deep.Ctx.selD_good
#audit_axioms_strict UND.Deep.Ctx.selD_good
#print axioms UND.Deep.Ctx.isPotential_psiD
#audit_axioms_strict UND.Deep.Ctx.isPotential_psiD
#print axioms UND.Deep.Ctx.inv_reach
#audit_axioms_strict UND.Deep.Ctx.inv_reach
#print axioms UND.Deep.Ctx.flag_of_termD
#audit_axioms_strict UND.Deep.Ctx.flag_of_termD
#print axioms UND.Deep.Ctx.gBin_add_level
#audit_axioms_strict UND.Deep.Ctx.gBin_add_level
#print axioms UND.Deep.Ctx.gLen_eq_gBinD
#audit_axioms_strict UND.Deep.Ctx.gLen_eq_gBinD
#print axioms UND.Deep.Ctx.armEdge_specD
#audit_axioms_strict UND.Deep.Ctx.armEdge_specD
#print axioms UND.Deep.card_nbrD_le
#audit_axioms_strict UND.Deep.card_nbrD_le
#print axioms UND.Deep.inGraphD_step
#audit_axioms_strict UND.Deep.inGraphD_step
#print axioms UND.Deep.not_isDiag_step
#audit_axioms_strict UND.Deep.not_isDiag_step
#print axioms UND.Deep.exists_deep_contour
#audit_axioms_strict UND.Deep.exists_deep_contour
#print axioms UND.Deep.deep_wrong
#audit_axioms_strict UND.Deep.deep_wrong
#print axioms UND.Deep.deep_wrong_lag
#audit_axioms_strict UND.Deep.deep_wrong_lag
#print axioms UND.Sensors.integrable_of_zero_one
#audit_axioms_strict UND.Sensors.integrable_of_zero_one
#print axioms UND.Sensors.mgf_le_of_zero_one
#audit_axioms_strict UND.Sensors.mgf_le_of_zero_one
#print axioms UND.Sensors.chernoff_zero_one
#audit_axioms_strict UND.Sensors.chernoff_zero_one
#print axioms UND.Sensors.chernoff_ratio
#audit_axioms_strict UND.Sensors.chernoff_ratio
#print axioms UND.Sensors.log_75_53
#audit_axioms_strict UND.Sensors.log_75_53
#print axioms UND.Sensors.log_four_gt
#audit_axioms_strict UND.Sensors.log_four_gt
#print axioms UND.Sensors.short_exponent
#audit_axioms_strict UND.Sensors.short_exponent
#print axioms UND.Sensors.exp_neg_le_two_zpow
#audit_axioms_strict UND.Sensors.exp_neg_le_two_zpow
#print axioms UND.Sensors.short_tail
#audit_axioms_strict UND.Sensors.short_tail
#print axioms UND.Sensors.hoeffding_zero_one
#audit_axioms_strict UND.Sensors.hoeffding_zero_one
#print axioms UND.Sensors.long_tail
#audit_axioms_strict UND.Sensors.long_tail
#print axioms UND.Sensors.geom_three_le
#audit_axioms_strict UND.Sensors.geom_three_le
#print axioms UND.Sensors.lower_law_gt
#audit_axioms_strict UND.Sensors.lower_law_gt
#print axioms UND.Sensors.ell_cast
#audit_axioms_strict UND.Sensors.ell_cast
#print axioms UND.Sensors.short_support_lt
#audit_axioms_strict UND.Sensors.short_support_lt
#print axioms UND.Sensors.uB_cast
#audit_axioms_strict UND.Sensors.uB_cast
#print axioms UND.Sensors.zB_cast
#audit_axioms_strict UND.Sensors.zB_cast
#print axioms UND.Sensors.wB_cast
#audit_axioms_strict UND.Sensors.wB_cast
#print axioms UND.Sensors.eta_bound
#audit_axioms_strict UND.Sensors.eta_bound
#print axioms UND.Sensors.etaHat_cast
#audit_axioms_strict UND.Sensors.etaHat_cast
#print axioms UND.Sensors.measurable_extend
#audit_axioms_strict UND.Sensors.measurable_extend
#print axioms UND.Sensors.extend_restrict
#audit_axioms_strict UND.Sensors.extend_restrict
#print axioms UND.Sensors.preimage_of_detBy
#audit_axioms_strict UND.Sensors.preimage_of_detBy
#print axioms UND.Sensors.infinitePi_inter_eq_mul
#audit_axioms_strict UND.Sensors.infinitePi_inter_eq_mul
#print axioms UND.Sensors.measurableSet_coord
#audit_axioms_strict UND.Sensors.measurableSet_coord
#print axioms UND.Sensors.set_mark
#audit_axioms_strict UND.Sensors.set_mark
#print axioms UND.Sensors.set_noflag
#audit_axioms_strict UND.Sensors.set_noflag
#print axioms UND.Sensors.measurableSet_rideEv
#audit_axioms_strict UND.Sensors.measurableSet_rideEv
#print axioms UND.Sensors.detBy_rideEv
#audit_axioms_strict UND.Sensors.detBy_rideEv
#print axioms UND.Sensors.infinitePi_coord
#audit_axioms_strict UND.Sensors.infinitePi_coord
#print axioms UND.Sensors.rideEv_real
#audit_axioms_strict UND.Sensors.rideEv_real
#print axioms UND.Sensors.uniformLaw_fieldSet
#audit_axioms_strict UND.Sensors.uniformLaw_fieldSet
#print axioms UND.Sensors.uniformLaw_upMark
#audit_axioms_strict UND.Sensors.uniformLaw_upMark
#print axioms UND.Sensors.uniformLaw_loMark
#audit_axioms_strict UND.Sensors.uniformLaw_loMark
#print axioms UND.Sensors.upper_law
#audit_axioms_strict UND.Sensors.upper_law
#print axioms UND.Sensors.lower_law
#audit_axioms_strict UND.Sensors.lower_law
#print axioms UND.Sensors.detBy_mono
#audit_axioms_strict UND.Sensors.detBy_mono
#print axioms UND.Sensors.detBy_empty
#audit_axioms_strict UND.Sensors.detBy_empty
#print axioms UND.Sensors.detBy_biInter
#audit_axioms_strict UND.Sensors.detBy_biInter
#print axioms UND.Sensors.detBy_biUnion
#audit_axioms_strict UND.Sensors.detBy_biUnion
#print axioms UND.Sensors.measurableSet_of_detBy
#audit_axioms_strict UND.Sensors.measurableSet_of_detBy
#print axioms UND.Sensors.infinitePi_biInter_eq_prod
#audit_axioms_strict UND.Sensors.infinitePi_biInter_eq_prod
#print axioms UND.Sensors.iIndepFun_of_detBy
#audit_axioms_strict UND.Sensors.iIndepFun_of_detBy
#print axioms UND.Sensors.laneAtom_inj
#audit_axioms_strict UND.Sensors.laneAtom_inj
#print axioms UND.Sensors.ride_length
#audit_axioms_strict UND.Sensors.ride_length
#print axioms UND.Sensors.ride_nodup
#audit_axioms_strict UND.Sensors.ride_nodup
#print axioms UND.Sensors.mem_ride
#audit_axioms_strict UND.Sensors.mem_ride
#print axioms UND.Sensors.ride_disjoint
#audit_axioms_strict UND.Sensors.ride_disjoint
#print axioms UND.Sensors.IsGate.lanePhase
#audit_axioms_strict UND.Sensors.IsGate.lanePhase
#print axioms UND.Sensors.isGate_of_end
#audit_axioms_strict UND.Sensors.isGate_of_end
#print axioms UND.Sensors.phaseZero_block
#audit_axioms_strict UND.Sensors.phaseZero_block
#print axioms UND.Sensors.depth_unique
#audit_axioms_strict UND.Sensors.depth_unique
#print axioms UND.Sensors.rightEnd_dvd
#audit_axioms_strict UND.Sensors.rightEnd_dvd
#print axioms UND.Sensors.rightEnd_eq
#audit_axioms_strict UND.Sensors.rightEnd_eq
#print axioms UND.Sensors.ell_lt_four_pow
#audit_axioms_strict UND.Sensors.ell_lt_four_pow
#print axioms UND.Sensors.ownership
#audit_axioms_strict UND.Sensors.ownership
#print axioms UND.Sensors.mem_gateAtoms
#audit_axioms_strict UND.Sensors.mem_gateAtoms
#print axioms UND.Sensors.gateAtoms_disjoint
#audit_axioms_strict UND.Sensors.gateAtoms_disjoint
#print axioms UND.Sensors.laneCount_congr
#audit_axioms_strict UND.Sensors.laneCount_congr
#print axioms UND.Sensors.detBy_shortBad
#audit_axioms_strict UND.Sensors.detBy_shortBad
#print axioms UND.Sensors.detBy_longBad
#audit_axioms_strict UND.Sensors.detBy_longBad
#print axioms UND.Sensors.laneInd_zero_one
#audit_axioms_strict UND.Sensors.laneInd_zero_one
#print axioms UND.Sensors.measurable_laneInd
#audit_axioms_strict UND.Sensors.measurable_laneInd
#print axioms UND.Sensors.sum_laneInd
#audit_axioms_strict UND.Sensors.sum_laneInd
#print axioms UND.Sensors.lanes_iIndep
#audit_axioms_strict UND.Sensors.lanes_iIndep
#print axioms UND.Sensors.upper_mean_le
#audit_axioms_strict UND.Sensors.upper_mean_le
#print axioms UND.Sensors.shortBad_le_of
#audit_axioms_strict UND.Sensors.shortBad_le_of
#print axioms UND.Sensors.longBad_le_of
#audit_axioms_strict UND.Sensors.longBad_le_of
#print axioms UND.Sensors.pLaw_eq
#audit_axioms_strict UND.Sensors.pLaw_eq
#print axioms UND.Sensors.isProbabilityMeasure_pLaw
#audit_axioms_strict UND.Sensors.isProbabilityMeasure_pLaw
#print axioms UND.Sensors.isProbabilityMeasure_noiseSite
#audit_axioms_strict UND.Sensors.isProbabilityMeasure_noiseSite
#print axioms UND.Sensors.shortBad_le
#audit_axioms_strict UND.Sensors.shortBad_le
#print axioms UND.Sensors.longBad_le
#audit_axioms_strict UND.Sensors.longBad_le
#print axioms UND.Sensors.biInter_union_subset
#audit_axioms_strict UND.Sensors.biInter_union_subset
#print axioms UND.Sensors.exists_big_class
#audit_axioms_strict UND.Sensors.exists_big_class
#print axioms UND.Sensors.min_le_sqrt_mul
#audit_axioms_strict UND.Sensors.min_le_sqrt_mul
#print axioms UND.Sensors.real_biInter_eq_prod
#audit_axioms_strict UND.Sensors.real_biInter_eq_prod
#print axioms UND.Sensors.joint_bound
#audit_axioms_strict UND.Sensors.joint_bound
#print axioms UND.Sensors.isRightEnd_iff
#audit_axioms_strict UND.Sensors.isRightEnd_iff
#print axioms UND.Sensors.card_ends_le
#audit_axioms_strict UND.Sensors.card_ends_le
#print axioms UND.Sensors.rawList_nodup
#audit_axioms_strict UND.Sensors.rawList_nodup
#print axioms UND.Sensors.rawList_length
#audit_axioms_strict UND.Sensors.rawList_length
#print axioms UND.Sensors.rawSupp_disjoint
#audit_axioms_strict UND.Sensors.rawSupp_disjoint
#print axioms UND.Sensors.rawEv_le
#audit_axioms_strict UND.Sensors.rawEv_le
#print axioms UND.Sensors.ell_mono
#audit_axioms_strict UND.Sensors.ell_mono
#print axioms UND.Sensors.Regime.ell_le
#audit_axioms_strict UND.Sensors.Regime.ell_le
#print axioms UND.Sensors.Regime.W_le_four
#audit_axioms_strict UND.Sensors.Regime.W_le_four
#print axioms UND.Sensors.detBy_gateBad
#audit_axioms_strict UND.Sensors.detBy_gateBad
#print axioms UND.Sensors.gateAtoms_sub_statSupp
#audit_axioms_strict UND.Sensors.gateAtoms_sub_statSupp
#print axioms UND.Sensors.detBy_statEv
#audit_axioms_strict UND.Sensors.detBy_statEv
#print axioms UND.Sensors.statSupp_disjoint
#audit_axioms_strict UND.Sensors.statSupp_disjoint
#print axioms UND.Sensors.statEv_le
#audit_axioms_strict UND.Sensors.statEv_le
#print axioms UND.Sensors.joint_source_bound
#audit_axioms_strict UND.Sensors.joint_source_bound
#print axioms UND.Sensors.Bparam_eq
#audit_axioms_strict UND.Sensors.Bparam_eq
#print axioms UND.Sensors.cden_ge
#audit_axioms_strict UND.Sensors.cden_ge
#print axioms UND.Sensors.C_le_hundredth
#audit_axioms_strict UND.Sensors.C_le_hundredth
#print axioms UND.Sensors.C_real_eq
#audit_axioms_strict UND.Sensors.C_real_eq
#print axioms UND.Sensors.regime_final
#audit_axioms_strict UND.Sensors.regime_final
#print axioms UND.Sensors.joint_source_final
#audit_axioms_strict UND.Sensors.joint_source_final
#print axioms UND.Contour.GroupedSystem.prop_of_mem_filter
#audit_axioms_strict UND.Contour.GroupedSystem.prop_of_mem_filter
#print axioms UND.Contour.GroupedSystem.grpEdges_card_le_lin
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdges_card_le_lin
#print axioms UND.Contour.GroupedSystem.armEdge_step
#audit_axioms_strict UND.Contour.GroupedSystem.armEdge_step
#print axioms UND.Contour.GroupedSystem.grpEdge_spec
#audit_axioms_strict UND.Contour.GroupedSystem.grpEdge_spec
#print axioms UND.Contour.GroupedSystem.mem_contour
#audit_axioms_strict UND.Contour.GroupedSystem.mem_contour
#print axioms UND.Contour.GroupedSystem.reach_image
#audit_axioms_strict UND.Contour.GroupedSystem.reach_image
#print axioms UND.Contour.GroupedSystem.reach_filter_not_diag
#audit_axioms_strict UND.Contour.GroupedSystem.reach_filter_not_diag
#print axioms UND.Contour.GroupedSystem.prepend
#audit_axioms_strict UND.Contour.GroupedSystem.prepend
#print axioms UND.Contour.GroupedSystem.mem_encoding_nonUN
#audit_axioms_strict UND.Contour.GroupedSystem.mem_encoding_nonUN
#print axioms UND.Contour.GroupedSystem.MemEnc.mono
#audit_axioms_strict UND.Contour.GroupedSystem.MemEnc.mono
#print axioms UND.Contour.GroupedSystem.MemEnc.isEncoding
#audit_axioms_strict UND.Contour.GroupedSystem.MemEnc.isEncoding
#print axioms UND.Contour.GroupedSystem.mem_encoding
#audit_axioms_strict UND.Contour.GroupedSystem.mem_encoding
#print axioms UND.Memory.mem_union
#audit_axioms_strict UND.Memory.mem_union
#print axioms UND.Memory.rep_field
#audit_axioms_strict UND.Memory.rep_field
#print axioms UND.Memory.rideVal_append
#audit_axioms_strict UND.Memory.rideVal_append
#print axioms UND.Memory.ride_succ
#audit_axioms_strict UND.Memory.ride_succ
#print axioms UND.Memory.rideEv_up_iff
#audit_axioms_strict UND.Memory.rideEv_up_iff
#print axioms UND.Memory.rideVal_of_rideEv_lo
#audit_axioms_strict UND.Memory.rideVal_of_rideEv_lo
#print axioms UND.Memory.chSite_sub_jy
#audit_axioms_strict UND.Memory.chSite_sub_jy
#print axioms UND.Memory.chSite_pred
#audit_axioms_strict UND.Memory.chSite_pred
#print axioms UND.Memory.chSite_add_jy
#audit_axioms_strict UND.Memory.chSite_add_jy
#print axioms UND.Memory.laneAtom_eq
#audit_axioms_strict UND.Memory.laneAtom_eq
#print axioms UND.Memory.copy_step
#audit_axioms_strict UND.Memory.copy_step
#print axioms UND.Memory.origin_step
#audit_axioms_strict UND.Memory.origin_step
#print axioms UND.Memory.ride_copy
#audit_axioms_strict UND.Memory.ride_copy
#print axioms UND.Memory.ride_short
#audit_axioms_strict UND.Memory.ride_short
#print axioms UND.Memory.gate_J
#audit_axioms_strict UND.Memory.gate_J
#print axioms UND.Memory.mem_filter'
#audit_axioms_strict UND.Memory.mem_filter'
#print axioms UND.Memory.hcount_short
#audit_axioms_strict UND.Memory.hcount_short
#print axioms UND.Memory.lcount_long
#audit_axioms_strict UND.Memory.lcount_long
#print axioms UND.Memory.one_le_T
#audit_axioms_strict UND.Memory.one_le_T
#print axioms UND.Memory.val_aV
#audit_axioms_strict UND.Memory.val_aV
#print axioms UND.Memory.qV_planar
#audit_axioms_strict UND.Memory.qV_planar
#print axioms UND.Memory.val_qV
#audit_axioms_strict UND.Memory.val_qV
#print axioms UND.Memory.rideBase_eq
#audit_axioms_strict UND.Memory.rideBase_eq
#print axioms UND.Memory.chSite_self
#audit_axioms_strict UND.Memory.chSite_self
#print axioms UND.Memory.chiOf_qV
#audit_axioms_strict UND.Memory.chiOf_qV
#print axioms UND.Memory.chiOf_rideBase
#audit_axioms_strict UND.Memory.chiOf_rideBase
#print axioms UND.Memory.chiOf_par
#audit_axioms_strict UND.Memory.chiOf_par
#print axioms UND.Memory.psi_eq_chi
#audit_axioms_strict UND.Memory.psi_eq_chi
#print axioms UND.Memory.supOf_aV
#audit_axioms_strict UND.Memory.supOf_aV
#print axioms UND.Memory.MCtx.exists_pgood
#audit_axioms_strict UND.Memory.MCtx.exists_pgood
#print axioms UND.Memory.MCtx.exists_pgood_of_NF
#audit_axioms_strict UND.Memory.MCtx.exists_pgood_of_NF
#print axioms UND.Memory.MCtx.pd_spec
#audit_axioms_strict UND.Memory.MCtx.pd_spec
#print axioms UND.Memory.MCtx.sel_spec
#audit_axioms_strict UND.Memory.MCtx.sel_spec
#print axioms UND.Memory.MCtx.sel_ne
#audit_axioms_strict UND.Memory.MCtx.sel_ne
#print axioms UND.Memory.MCtx.unM_spec
#audit_axioms_strict UND.Memory.MCtx.unM_spec
#print axioms UND.Memory.MCtx.rk_lt_of
#audit_axioms_strict UND.Memory.MCtx.rk_lt_of
#print axioms UND.Memory.MCtx.rk_sup
#audit_axioms_strict UND.Memory.MCtx.rk_sup
#print axioms UND.Memory.MCtx.rk_un
#audit_axioms_strict UND.Memory.MCtx.rk_un
#print axioms UND.Memory.MCtx.sel_good
#audit_axioms_strict UND.Memory.MCtx.sel_good
#print axioms UND.Memory.MCtx.isPotential_sysM
#audit_axioms_strict UND.Memory.MCtx.isPotential_sysM
#print axioms UND.Memory.MCtx.hgrp_sysM
#audit_axioms_strict UND.Memory.MCtx.hgrp_sysM
#print axioms UND.Memory.MCtx.hUUU_sysM
#audit_axioms_strict UND.Memory.MCtx.hUUU_sysM
#print axioms UND.Memory.ind_decide
#audit_axioms_strict UND.Memory.ind_decide
#print axioms UND.Memory.card_nbrM_le
#audit_axioms_strict UND.Memory.card_nbrM_le
#print axioms UND.Memory.nbrM_le_Delta
#audit_axioms_strict UND.Memory.nbrM_le_Delta
#print axioms UND.Memory.mem_nbrM_fwdS
#audit_axioms_strict UND.Memory.mem_nbrM_fwdS
#print axioms UND.Memory.mem_nbrM_bwdS
#audit_axioms_strict UND.Memory.mem_nbrM_bwdS
#print axioms UND.Memory.mem_nbrM_fwdU
#audit_axioms_strict UND.Memory.mem_nbrM_fwdU
#print axioms UND.Memory.mem_nbrM_bwdU
#audit_axioms_strict UND.Memory.mem_nbrM_bwdU
#print axioms UND.Memory.bin_cases
#audit_axioms_strict UND.Memory.bin_cases
#print axioms UND.Memory.bin_ind
#audit_axioms_strict UND.Memory.bin_ind
#print axioms UND.Memory.fM_eq_iff
#audit_axioms_strict UND.Memory.fM_eq_iff
#print axioms UND.Memory.outT_supOf
#audit_axioms_strict UND.Memory.outT_supOf
#print axioms UND.Memory.outT_zero
#audit_axioms_strict UND.Memory.outT_zero
#print axioms UND.Memory.outT_qV
#audit_axioms_strict UND.Memory.outT_qV
#print axioms UND.Memory.outT_aV
#audit_axioms_strict UND.Memory.outT_aV
#print axioms UND.Memory.MCtx.step_nbr
#audit_axioms_strict UND.Memory.MCtx.step_nbr
#print axioms UND.Memory.MCtx.bad_of_reach
#audit_axioms_strict UND.Memory.MCtx.bad_of_reach
#print axioms UND.Memory.mem_rideEv_true
#audit_axioms_strict UND.Memory.mem_rideEv_true
#print axioms UND.Memory.MCtx.bad_zero_iff
#audit_axioms_strict UND.Memory.MCtx.bad_zero_iff
#print axioms UND.Memory.MCtx.drvA_good
#audit_axioms_strict UND.Memory.MCtx.drvA_good
#print axioms UND.Memory.MCtx.drvQ_good
#audit_axioms_strict UND.Memory.MCtx.drvQ_good
#print axioms UND.Memory.MCtx.chSite_ride_planar
#audit_axioms_strict UND.Memory.MCtx.chSite_ride_planar
#print axioms UND.Memory.MCtx.term_source
#audit_axioms_strict UND.Memory.MCtx.term_source
#print axioms UND.Memory.MCtx.mem_cover
#audit_axioms_strict UND.Memory.MCtx.mem_cover
#print axioms UND.Memory.gamma_facts
#audit_axioms_strict UND.Memory.gamma_facts
#print axioms UND.Memory.tsum_ofReal_mem
#audit_axioms_strict UND.Memory.tsum_ofReal_mem
#print axioms UND.Memory.joint_MP
#audit_axioms_strict UND.Memory.joint_MP
#print axioms UND.Memory.mem_bad_le
#audit_axioms_strict UND.Memory.mem_bad_le
#print axioms UND.Memory.isLegalBlock_blockAt
#audit_axioms_strict UND.Memory.isLegalBlock_blockAt
#print axioms UND.Memory.liftSym_eq
#audit_axioms_strict UND.Memory.liftSym_eq
#print axioms UND.Memory.ctr_liftChart
#audit_axioms_strict UND.Memory.ctr_liftChart
#print axioms UND.Memory.liftChart_full
#audit_axioms_strict UND.Memory.liftChart_full
#print axioms UND.Memory.leftEnd_back
#audit_axioms_strict UND.Memory.leftEnd_back
#print axioms UND.Memory.chart_gate
#audit_axioms_strict UND.Memory.chart_gate
#print axioms UND.Memory.firstHit_cons
#audit_axioms_strict UND.Memory.firstHit_cons
#print axioms UND.Memory.firstHit_map
#audit_axioms_strict UND.Memory.firstHit_map
#print axioms UND.Memory.measurableSet_firstHit
#audit_axioms_strict UND.Memory.measurableSet_firstHit
#print axioms UND.Memory.chainSite_zero
#audit_axioms_strict UND.Memory.chainSite_zero
#print axioms UND.Memory.chainSite_succ
#audit_axioms_strict UND.Memory.chainSite_succ
#print axioms UND.Memory.chainSite_add
#audit_axioms_strict UND.Memory.chainSite_add
#print axioms UND.Memory.valX_succ
#audit_axioms_strict UND.Memory.valX_succ
#print axioms UND.Memory.initField_rec
#audit_axioms_strict UND.Memory.initField_rec
#print axioms UND.Memory.decode_encode
#audit_axioms_strict UND.Memory.decode_encode
#print axioms UND.Memory.encode_decode
#audit_axioms_strict UND.Memory.encode_decode
#print axioms UND.Memory.pastOf_zero
#audit_axioms_strict UND.Memory.pastOf_zero
#print axioms UND.Memory.X0_eq
#audit_axioms_strict UND.Memory.X0_eq
#print axioms UND.Memory.hyb_nonpos
#audit_axioms_strict UND.Memory.hyb_nonpos
#print axioms UND.Memory.hyb_nat
#audit_axioms_strict UND.Memory.hyb_nat
#print axioms UND.Memory.hyb_succ
#audit_axioms_strict UND.Memory.hyb_succ
#print axioms UND.Memory.hyb_hyp
#audit_axioms_strict UND.Memory.hyb_hyp
#print axioms UND.Memory.measurable_X0
#audit_axioms_strict UND.Memory.measurable_X0
#print axioms UND.Memory.X0_shift
#audit_axioms_strict UND.Memory.X0_shift
#print axioms UND.Memory.isProbabilityMeasure_initLaw
#audit_axioms_strict UND.Memory.isProbabilityMeasure_initLaw
#print axioms UND.Memory.initLaw_TI
#audit_axioms_strict UND.Memory.initLaw_TI
#print axioms UND.Memory.measurable_glue
#audit_axioms_strict UND.Memory.measurable_glue
#print axioms UND.Memory.negPart_glue
#audit_axioms_strict UND.Memory.negPart_glue
#print axioms UND.Memory.posPart_glue
#audit_axioms_strict UND.Memory.posPart_glue
#print axioms UND.Memory.measurable_negPart
#audit_axioms_strict UND.Memory.measurable_negPart
#print axioms UND.Memory.measurable_posPart
#audit_axioms_strict UND.Memory.measurable_posPart
#print axioms UND.Memory.glue_law
#audit_axioms_strict UND.Memory.glue_law
#print axioms UND.Memory.encode_hyb
#audit_axioms_strict UND.Memory.encode_hyb
#print axioms UND.Memory.law_initLaw
#audit_axioms_strict UND.Memory.law_initLaw
#print axioms UND.Memory.Smem_nonneg
#audit_axioms_strict UND.Memory.Smem_nonneg
#print axioms UND.Memory.Smem_lt
#audit_axioms_strict UND.Memory.Smem_lt
#print axioms UND.Memory.law_initLaw_le
#audit_axioms_strict UND.Memory.law_initLaw_le
#print axioms UND.Memory.one_le_n0
#audit_axioms_strict UND.Memory.one_le_n0
#print axioms UND.Memory.nhalt_cutOf
#audit_axioms_strict UND.Memory.nhalt_cutOf
#print axioms UND.Memory.liftSym_eq_liftB
#audit_axioms_strict UND.Memory.liftSym_eq_liftB
#print axioms UND.Memory.measurableSet_cSf
#audit_axioms_strict UND.Memory.measurableSet_cSf
#print axioms UND.Memory.cSf_shift
#audit_axioms_strict UND.Memory.cSf_shift
#print axioms UND.Memory.memLaw_prob
#audit_axioms_strict UND.Memory.memLaw_prob
#print axioms UND.Memory.memLaw_TI
#audit_axioms_strict UND.Memory.memLaw_TI
#print axioms UND.Memory.hyp_typical
#audit_axioms_strict UND.Memory.hyp_typical
#print axioms UND.Memory.law_memLaw_le
#audit_axioms_strict UND.Memory.law_memLaw_le
#print axioms UND.Memory.zero_mem_win0
#audit_axioms_strict UND.Memory.zero_mem_win0
#print axioms UND.Memory.mem_cyl_liveOne
#audit_axioms_strict UND.Memory.mem_cyl_liveOne
#print axioms UND.Memory.memory_branch
#audit_axioms_strict UND.Memory.memory_branch
#print axioms UND.Memory.theorem_7_3
#audit_axioms_strict UND.Memory.theorem_7_3
#print axioms UND.Memory.theoremA_of_halting
#audit_axioms_strict UND.Memory.theoremA_of_halting
#print axioms UND.Forget.helperTraj_of_complete
#audit_axioms_strict UND.Forget.helperTraj_of_complete
#print axioms UND.Forget.data_of_complete
#audit_axioms_strict UND.Forget.data_of_complete
#print axioms UND.Forget.isub_refl
#audit_axioms_strict UND.Forget.isub_refl
#print axioms UND.Forget.isub_both
#audit_axioms_strict UND.Forget.isub_both
#print axioms UND.Forget.isub_withZero
#audit_axioms_strict UND.Forget.isub_withZero
#print axioms UND.Forget.isub_zero_withZero
#audit_axioms_strict UND.Forget.isub_zero_withZero
#print axioms UND.Forget.hasOne_of_isub
#audit_axioms_strict UND.Forget.hasOne_of_isub
#print axioms UND.Forget.eq_one_of_isub
#audit_axioms_strict UND.Forget.eq_one_of_isub
#print axioms UND.Forget.mono_step
#audit_axioms_strict UND.Forget.mono_step
#print axioms UND.Forget.mono_origin
#audit_axioms_strict UND.Forget.mono_origin
#print axioms UND.Forget.ride_mono
#audit_axioms_strict UND.Forget.ride_mono
#print axioms UND.Forget.ride_mono_short
#audit_axioms_strict UND.Forget.ride_mono_short
#print axioms UND.Forget.lcount_le_short
#audit_axioms_strict UND.Forget.lcount_le_short
#print axioms UND.Forget.lo_le_hcount
#audit_axioms_strict UND.Forget.lo_le_hcount
#print axioms UND.Forget.missed_erasure
#audit_axioms_strict UND.Forget.missed_erasure
#print axioms UND.Forget.isRChart_ctr
#audit_axioms_strict UND.Forget.isRChart_ctr
#print axioms UND.Forget.gate_facts
#audit_axioms_strict UND.Forget.gate_facts
#print axioms UND.Forget.halting_gate
#audit_axioms_strict UND.Forget.halting_gate
#print axioms UND.Forget.nxt_time
#audit_axioms_strict UND.Forget.nxt_time
#print axioms UND.Forget.flagSet_time
#audit_axioms_strict UND.Forget.flagSet_time
#print axioms UND.Forget.card_flagSet
#audit_axioms_strict UND.Forget.card_flagSet
#print axioms UND.Forget.wt_eq
#audit_axioms_strict UND.Forget.wt_eq
#print axioms UND.Forget.atomSet_time
#audit_axioms_strict UND.Forget.atomSet_time
#print axioms UND.Forget.detBy_badSet
#audit_axioms_strict UND.Forget.detBy_badSet
#print axioms UND.Forget.measure_badSet_le
#audit_axioms_strict UND.Forget.measure_badSet_le
#print axioms UND.Forget.le_mul_pow_three
#audit_axioms_strict UND.Forget.le_mul_pow_three
#print axioms UND.Forget.measure_WEv_le
#audit_axioms_strict UND.Forget.measure_WEv_le
#print axioms UND.Forget.tsum_wt_le
#audit_axioms_strict UND.Forget.tsum_wt_le
#print axioms UND.Forget.path_disp
#audit_axioms_strict UND.Forget.path_disp
#print axioms UND.Forget.exists_witness
#audit_axioms_strict UND.Forget.exists_witness
#print axioms UND.Forget.card_boxP
#audit_axioms_strict UND.Forget.card_boxP
#print axioms UND.Forget.card_flagSets_le
#audit_axioms_strict UND.Forget.card_flagSets_le
#print axioms UND.Forget.blkW_le
#audit_axioms_strict UND.Forget.blkW_le
#print axioms UND.Forget.blk_sum_le
#audit_axioms_strict UND.Forget.blk_sum_le
#print axioms UND.Forget.hpath_null
#audit_axioms_strict UND.Forget.hpath_null
#print axioms UND.Forget.pow_four_le
#audit_axioms_strict UND.Forget.pow_four_le
#print axioms UND.Forget.term_le
#audit_axioms_strict UND.Forget.term_le
#print axioms UND.Forget.sqrt_sqrt_facts
#audit_axioms_strict UND.Forget.sqrt_sqrt_facts
#print axioms UND.Forget.hist_base
#audit_axioms_strict UND.Forget.hist_base
#print axioms UND.Forget.chSite_node
#audit_axioms_strict UND.Forget.chSite_node
#print axioms UND.Forget.detBy_badK
#audit_axioms_strict UND.Forget.detBy_badK
#print axioms UND.Forget.atomsK_disjoint
#audit_axioms_strict UND.Forget.atomsK_disjoint
#print axioms UND.Forget.uld_back
#audit_axioms_strict UND.Forget.uld_back
#print axioms UND.Forget.node_prop
#audit_axioms_strict UND.Forget.node_prop
#print axioms UND.Forget.hpath_of_ul
#audit_axioms_strict UND.Forget.hpath_of_ul
#print axioms UND.Forget.no_ul_generic
#audit_axioms_strict UND.Forget.no_ul_generic
#print axioms UND.Forget.proposal_of_dead
#audit_axioms_strict UND.Forget.proposal_of_dead
#print axioms UND.Forget.live_marked
#audit_axioms_strict UND.Forget.live_marked
#print axioms UND.Forget.disc_step
#audit_axioms_strict UND.Forget.disc_step
#print axioms UND.Forget.flagged_complete
#audit_axioms_strict UND.Forget.flagged_complete
#print axioms UND.Forget.card_nbC_le
#audit_axioms_strict UND.Forget.card_nbC_le
#print axioms UND.Forget.par_chi
#audit_axioms_strict UND.Forget.par_chi
#print axioms UND.Forget.nbr_symm
#audit_axioms_strict UND.Forget.nbr_symm
#print axioms UND.Forget.nbC_symm
#audit_axioms_strict UND.Forget.nbC_symm
#print axioms UND.Forget.nbr_sub_nbC
#audit_axioms_strict UND.Forget.nbr_sub_nbC
#print axioms UND.Forget.conEdge_card
#audit_axioms_strict UND.Forget.conEdge_card
#print axioms UND.Forget.conEdge_reach
#audit_axioms_strict UND.Forget.conEdge_reach
#print axioms UND.Forget.conEdge_connected
#audit_axioms_strict UND.Forget.conEdge_connected
#print axioms UND.Forget.conEdge_inGraph
#audit_axioms_strict UND.Forget.conEdge_inGraph
#print axioms UND.Forget.pathEdges_inGraphC
#audit_axioms_strict UND.Forget.pathEdges_inGraphC
#print axioms UND.Forget.inGraph_unionC
#audit_axioms_strict UND.Forget.inGraph_unionC
#print axioms UND.Forget.inGraph_nbr_C
#audit_axioms_strict UND.Forget.inGraph_nbr_C
#print axioms UND.Forget.exists_cover_C
#audit_axioms_strict UND.Forget.exists_cover_C
#print axioms UND.Forget.degree_le_rare
#audit_axioms_strict UND.Forget.degree_le_rare
#print axioms UND.Forget.discEv_null
#audit_axioms_strict UND.Forget.discEv_null
#print axioms UND.Forget.coupling_generic
#audit_axioms_strict UND.Forget.coupling_generic
#print axioms UND.Forget.gateOracle_theCA
#audit_axioms_strict UND.Forget.gateOracle_theCA
#print axioms UND.Forget.Khist_facts
#audit_axioms_strict UND.Forget.Khist_facts
#print axioms UND.Forget.halting_branch_gen
#audit_axioms_strict UND.Forget.halting_branch_gen
#print axioms UND.Forget.gate_bounds_final
#audit_axioms_strict UND.Forget.gate_bounds_final
#print axioms UND.Forget.eta_final
#audit_axioms_strict UND.Forget.eta_final
#print axioms UND.Forget.eps_hist_final
#audit_axioms_strict UND.Forget.eps_hist_final
#print axioms UND.Forget.rare_of
#audit_axioms_strict UND.Forget.rare_of
#print axioms UND.Forget.rare_final
#audit_axioms_strict UND.Forget.rare_final
#print axioms UND.Forget.halting_branch
#audit_axioms_strict UND.Forget.halting_branch

/-! Complete imported audit, including generated and private declarations. -/
set_option maxHeartbeats 20000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut coreCount := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx]!
      let s := mod.toString
      let own := s.startsWith "UncomputableNoiseDiagram"
      let core := s.startsWith "FixedNoiseErgodicity" || s.startsWith "UndecidablePhaseDiagram"
      if own || core then
        if ci matches .axiomInfo _ then throwError "Axiom declaration {n} in {mod}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        if own then
          logInfo m!"UND_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          count := count + 1
        else
          logInfo m!"CORE_DECL:{toJson (n.toString, s, ax.map Name.toString) |>.compress}"
          coreCount := coreCount + 1
  let check (n : Name) (t : Expr) : CommandElabM Unit := do
    let some ci := env.find? n | throwError "Missing {n}"
    unless ci matches .thmInfo _ do throwError "{n} is not a theorem"
    unless ci.type == t do throwError "{n} statement changed"
  check ``UND.theorem_A (mkConst ``UND.TheoremA)
  check ``UND.corollary_9_4 (mkConst ``UND.CorollaryNineFour)
  check ``UND.one_rule_undecidable (mkConst ``UND.OneRuleUndecidable)
  logInfo m!"UND_FINAL_TYPES_OK"
  logInfo m!"UND_DECL_COUNT:{count}"
  logInfo m!"CORE_DECL_COUNT:{coreCount}"
