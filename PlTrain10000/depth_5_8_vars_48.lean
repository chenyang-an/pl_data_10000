variable (p0 p3 p5 : Prop)
theorem file48_35 : ((((((False ∧ p0) → False) → False) → (((p3 → False) → (True → False)) → ((p5 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((False ∧ p0) → False) → False) → (((p3 → False) → (True → False)) → ((p5 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_27 : ((False ∧ p0) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
    let assump_14 := assump_5 assump_27
    apply False.elim assump_14
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p2 p7 p5 p1 p6 p4 p0 : Prop)
theorem file48_720 : ((((((p1 → False) → (p1 → p4)) ∨ ((p2 → p4) ∧ (p0 → False))) ∨ (((p1 ∧ p0) ∨ (p1 ∨ p5)) → ((p7 → p4) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) → (p1 → p4)) ∨ ((p2 → p4) ∧ (p0 → False))) ∨ (((p1 ∧ p0) ∨ (p1 ∨ p5)) → ((p7 → p4) → (p6 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : p1 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p1 p3 p6 : Prop)
theorem file48_1335 : (((((True ∧ False) → False) → False) → False) ∨ ((((p6 → False) → (p0 ∨ p3)) ∧ ((p6 → p3) → False)) → (((p6 ∨ p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p7 p4 : Prop)
theorem file48_1779 : ((((((p1 ∧ p1) ∨ (p7 ∨ True)) ∧ ((True → False) → False)) ∧ (((True → False) → False) ∨ ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p1 ∧ p1) ∨ (p7 ∨ True)) ∧ ((True → False) → False)) ∧ (((True → False) → False) ∨ ((p4 → False) → False))) := by
    apply And.intro
    apply And.intro
    apply Or.inr
    apply Or.inr
    apply True.intro
    intro assump_5
    have assump_23 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
    apply Or.inl
    intro assump_12
    have assump_24 : True := by
      apply True.intro
    let assump_15 := assump_12 assump_24
    apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p4 p2 p0 p6 p1 : Prop)
theorem file48_2596 : ((((((True → False) ∨ (p4 → p4)) ∨ ((False → False) ∧ (p0 ∧ p4))) ∧ (((p1 ∧ p6) → False) ∨ ((True → p6) ∧ (p1 → p2)))) ∧ ((((p7 ∨ True) → (False ∧ p0)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case inl assump_12 =>
            have assump_138 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
              intro assump_19
              have assump_139 : (p7 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_22 := assump_19 assump_139
              let assump_23 := And.left assump_22
              apply False.elim assump_23
            let assump_18 := assump_3 assump_138
            apply False.elim assump_18
          case inr assump_13 =>
            cases assump_13
            case intro assump_30 assump_31 =>
              have assump_140 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
                intro assump_39
                have assump_141 : (p7 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_42 := assump_39 assump_141
                let assump_43 := And.left assump_42
                apply False.elim assump_43
              let assump_38 := assump_3 assump_140
              apply False.elim assump_38
        case inr assump_9 =>
          cases assump_5
          case inl assump_52 =>
            have assump_142 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
              intro assump_59
              have assump_143 : (p7 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_62 := assump_59 assump_143
              let assump_63 := And.left assump_62
              apply False.elim assump_63
            let assump_58 := assump_3 assump_142
            apply False.elim assump_58
          case inr assump_53 =>
            cases assump_53
            case intro assump_70 assump_71 =>
              have assump_144 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
                intro assump_79
                have assump_145 : (p7 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_82 := assump_79 assump_145
                let assump_83 := And.left assump_82
                apply False.elim assump_83
              let assump_78 := assump_3 assump_144
              apply False.elim assump_78
      case inr assump_7 =>
        cases assump_7
        case intro assump_90 assump_91 =>
          cases assump_91
          case intro assump_94 assump_95 =>
            cases assump_5
            case inl assump_100 =>
              have assump_146 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
                intro assump_107
                have assump_147 : (p7 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_110 := assump_107 assump_147
                let assump_111 := And.left assump_110
                apply False.elim assump_111
              let assump_106 := assump_3 assump_146
              apply False.elim assump_106
            case inr assump_101 =>
              cases assump_101
              case intro assump_118 assump_119 =>
                have assump_148 : (((p7 ∨ True) → (False ∧ p0)) → False) := by
                  intro assump_127
                  have assump_149 : (p7 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_130 := assump_127 assump_149
                  let assump_131 := And.left assump_130
                  apply False.elim assump_131
                let assump_126 := assump_3 assump_148
                apply False.elim assump_126


variable (p3 p7 p1 p4 p2 p6 p5 p0 : Prop)
theorem file48_6570 : (((((True ∨ p2) → (False ∧ p0)) ∨ ((p3 ∨ p3) → (False ∨ p4))) ∧ (((p1 → p6) → (p5 → p6)) → ((p7 ∨ p2) ∧ (p4 → False)))) → ((((p2 ∧ p3) ∨ (True ∨ p3)) ∧ ((p1 ∧ False) → (True → p1))) ∨ (((p5 → False) → (p7 ∨ p0)) ∧ ((p0 ∨ True) ∨ (p1 → p2))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply And.intro
      apply Or.inr
      apply Or.inl
      apply True.intro
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    case inr assump_5 =>
      apply Or.inl
      apply And.intro
      apply Or.inr
      apply Or.inl
      apply True.intro
      intro assump_24
      intro assump_25
      cases assump_24
      case intro assump_28 assump_29 =>
        apply False.elim assump_29


variable (p7 p4 p3 p0 p6 : Prop)
theorem file48_7499 : ((((((False → False) → (p0 ∨ p7)) → ((True ∧ p0) → (False → p3))) ∨ (((p6 → False) ∧ (p4 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False → False) → (p0 ∨ p7)) → ((True ∧ p0) → (False → p3))) ∨ (((p6 → False) ∧ (p4 → p3)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p2 p1 p3 p7 p4 p0 : Prop)
theorem file48_8007 : (((((p7 ∧ False) ∧ (p3 → False)) → False) ∨ (((p7 → p7) ∨ (p1 → False)) → False)) → ((((p2 ∧ p0) → (True → p0)) ∧ ((p0 ∧ p5) ∨ (p5 ∨ p1))) ∨ (((False ∧ p4) ∧ (p5 → p5)) → ((False ∧ p3) → (p2 ∧ p0))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    intro assump_16
    intro assump_17
    apply And.intro
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_18
    cases assump_17
    case intro assump_22 assump_23 =>
      apply False.elim assump_22
  case inr assump_3 =>
    apply Or.inr
    intro assump_38
    intro assump_39
    apply And.intro
    cases assump_39
    case intro assump_40 assump_41 =>
      apply False.elim assump_40
    cases assump_39
    case intro assump_44 assump_45 =>
      apply False.elim assump_44


variable (p1 p4 : Prop)
theorem file48_8860 : (((((True → False) ∧ (p1 → p4)) → False) → False) → False) := by
  intro assump_14
  have assump_33 : (((True → False) ∧ (p1 → p4)) → False) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      have assump_34 : True := by
        apply True.intro
      let assump_26 := assump_19 assump_34
      apply False.elim assump_26
  let assump_17 := assump_14 assump_33
  apply False.elim assump_17


variable (p7 p3 p6 p2 p1 p0 p4 : Prop)
theorem file48_9351 : ((((((p6 → p0) ∨ (p6 ∧ p0)) → False) ∧ (((True ∧ False) ∧ (p2 ∨ p1)) → ((p6 ∧ p4) → (True → p3)))) ∧ ((((p0 ∨ True) → False) → ((p7 → p0) ∧ (p1 ∨ p6))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      have assump_40 : (((p0 ∨ True) → False) → ((p7 → p0) ∧ (p1 ∨ p6))) := by
        intro assump_21
        apply And.intro
        intro assump_22
        have assump_41 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_27 := assump_21 assump_41
        apply False.elim assump_27
        have assump_42 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_33 := assump_21 assump_42
        apply False.elim assump_33
      let assump_20 := assump_11 assump_40
      apply False.elim assump_20


variable (p0 p5 p1 p7 p4 p3 p2 : Prop)
theorem file48_10292 : (((((True → False) ∨ (p1 ∨ True)) ∨ ((p0 → p7) → False)) ∧ (((p7 ∨ p5) ∧ (p3 → p0)) ∧ ((p7 ∨ p5) → False))) → ((((p4 ∨ p5) ∧ (p3 → p2)) ∨ ((p1 ∧ p5) → False)) ∧ (((p4 → False) → (p1 → False)) → False))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              apply Or.inr
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                have assump_297 : (p7 ∨ p5) := by
                  apply Or.inl
                  exact assump_14
                let assump_31 := assump_11 assump_297
                apply False.elim assump_31
            case inr assump_15 =>
              apply Or.inl
              apply And.intro
              apply Or.inr
              exact assump_15
              intro assump_41
              have assump_298 : (p7 ∨ p5) := by
                apply Or.inr
                exact assump_15
              let assump_45 := assump_11 assump_298
              apply False.elim assump_45
      case inr assump_7 =>
        cases assump_7
        case inl assump_49 =>
          cases assump_3
          case intro assump_53 assump_54 =>
            cases assump_53
            case intro assump_55 assump_56 =>
              cases assump_55
              case inl assump_57 =>
                apply Or.inr
                intro assump_65
                cases assump_65
                case intro assump_66 assump_67 =>
                  have assump_299 : (p7 ∨ p5) := by
                    apply Or.inl
                    exact assump_57
                  let assump_74 := assump_54 assump_299
                  apply False.elim assump_74
              case inr assump_58 =>
                apply Or.inl
                apply And.intro
                apply Or.inr
                exact assump_58
                intro assump_84
                have assump_300 : (p7 ∨ p5) := by
                  apply Or.inr
                  exact assump_58
                let assump_88 := assump_54 assump_300
                apply False.elim assump_88
        case inr assump_50 =>
          cases assump_3
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_96
              case inl assump_98 =>
                apply Or.inr
                intro assump_106
                cases assump_106
                case intro assump_107 assump_108 =>
                  have assump_301 : (p7 ∨ p5) := by
                    apply Or.inl
                    exact assump_98
                  let assump_115 := assump_95 assump_301
                  apply False.elim assump_115
              case inr assump_99 =>
                apply Or.inl
                apply And.intro
                apply Or.inr
                exact assump_99
                intro assump_125
                have assump_302 : (p7 ∨ p5) := by
                  apply Or.inr
                  exact assump_99
                let assump_129 := assump_95 assump_302
                apply False.elim assump_129
    case inr assump_5 =>
      cases assump_3
      case intro assump_135 assump_136 =>
        cases assump_135
        case intro assump_137 assump_138 =>
          cases assump_137
          case inl assump_139 =>
            apply Or.inr
            intro assump_147
            cases assump_147
            case intro assump_148 assump_149 =>
              have assump_303 : (p7 ∨ p5) := by
                apply Or.inl
                exact assump_139
              let assump_156 := assump_136 assump_303
              apply False.elim assump_156
          case inr assump_140 =>
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_140
            intro assump_166
            have assump_304 : (p7 ∨ p5) := by
              apply Or.inr
              exact assump_140
            let assump_170 := assump_136 assump_304
            apply False.elim assump_170
  intro assump_174
  cases assump_1
  case intro assump_177 assump_178 =>
    cases assump_177
    case inl assump_179 =>
      cases assump_179
      case inl assump_181 =>
        cases assump_178
        case intro assump_185 assump_186 =>
          cases assump_185
          case intro assump_187 assump_188 =>
            cases assump_187
            case inl assump_189 =>
              have assump_305 : (p7 ∨ p5) := by
                apply Or.inl
                exact assump_189
              let assump_197 := assump_186 assump_305
              apply False.elim assump_197
            case inr assump_190 =>
              have assump_306 : (p7 ∨ p5) := by
                apply Or.inr
                exact assump_190
              let assump_207 := assump_186 assump_306
              apply False.elim assump_207
      case inr assump_182 =>
        cases assump_182
        case inl assump_211 =>
          cases assump_178
          case intro assump_215 assump_216 =>
            cases assump_215
            case intro assump_217 assump_218 =>
              cases assump_217
              case inl assump_219 =>
                have assump_307 : (p7 ∨ p5) := by
                  apply Or.inl
                  exact assump_219
                let assump_227 := assump_216 assump_307
                apply False.elim assump_227
              case inr assump_220 =>
                have assump_308 : (p7 ∨ p5) := by
                  apply Or.inr
                  exact assump_220
                let assump_237 := assump_216 assump_308
                apply False.elim assump_237
        case inr assump_212 =>
          cases assump_178
          case intro assump_243 assump_244 =>
            cases assump_243
            case intro assump_245 assump_246 =>
              cases assump_245
              case inl assump_247 =>
                have assump_309 : (p7 ∨ p5) := by
                  apply Or.inl
                  exact assump_247
                let assump_255 := assump_244 assump_309
                apply False.elim assump_255
              case inr assump_248 =>
                have assump_310 : (p7 ∨ p5) := by
                  apply Or.inr
                  exact assump_248
                let assump_265 := assump_244 assump_310
                apply False.elim assump_265
    case inr assump_180 =>
      cases assump_178
      case intro assump_271 assump_272 =>
        cases assump_271
        case intro assump_273 assump_274 =>
          cases assump_273
          case inl assump_275 =>
            have assump_311 : (p7 ∨ p5) := by
              apply Or.inl
              exact assump_275
            let assump_283 := assump_272 assump_311
            apply False.elim assump_283
          case inr assump_276 =>
            have assump_312 : (p7 ∨ p5) := by
              apply Or.inr
              exact assump_276
            let assump_293 := assump_272 assump_312
            apply False.elim assump_293


variable (p2 p0 p5 p3 p6 p1 p7 p4 : Prop)
theorem file48_17622 : ((((((p5 ∨ p0) ∨ (True → p3)) → False) → (((p7 → False) ∨ (False ∧ p5)) → ((p6 ∨ p1) ∧ (True ∧ True)))) ∧ ((((True ∨ p4) ∨ (p2 ∧ p4)) ∨ ((p4 → p6) → (p4 ∧ p1))) → False)) → False) := by
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    have assump_33 : (((True ∨ p4) ∨ (p2 ∧ p4)) ∨ ((p4 → p6) → (p4 ∧ p1))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_29 := assump_24 assump_33
    apply False.elim assump_29


variable (p1 p6 p3 p5 p4 p2 p7 p0 : Prop)
theorem file48_18179 : (((((False → p2) → False) ∨ ((p0 → False) → (False ∨ True))) ∨ (((p2 → False) → (p4 ∧ True)) ∧ ((p1 → p5) ∧ (p4 ∧ p1)))) → ((((p6 ∨ p5) ∧ (p7 ∧ p2)) ∨ ((p6 → False) → False)) → (((p4 ∧ p1) ∨ (p3 → True)) ∨ ((p4 ∧ p6) ∨ (p5 → False))))) := by
  intro assump_14
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        cases assump_19
        case intro assump_24 assump_25 =>
          cases assump_14
          case inl assump_30 =>
            cases assump_30
            case inl assump_32 =>
              apply Or.inl
              apply Or.inr
              intro assump_36
              apply True.intro
            case inr assump_33 =>
              apply Or.inl
              apply Or.inr
              intro assump_39
              apply True.intro
          case inr assump_31 =>
            cases assump_31
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                cases assump_45
                case intro assump_48 assump_49 =>
                  apply Or.inl
                  apply Or.inl
                  apply And.intro
                  exact assump_48
                  exact assump_49
      case inr assump_21 =>
        cases assump_19
        case intro assump_56 assump_57 =>
          cases assump_14
          case inl assump_62 =>
            cases assump_62
            case inl assump_64 =>
              apply Or.inl
              apply Or.inr
              intro assump_68
              apply True.intro
            case inr assump_65 =>
              apply Or.inl
              apply Or.inr
              intro assump_71
              apply True.intro
          case inr assump_63 =>
            cases assump_63
            case intro assump_72 assump_73 =>
              cases assump_73
              case intro assump_76 assump_77 =>
                cases assump_77
                case intro assump_80 assump_81 =>
                  apply Or.inl
                  apply Or.inl
                  apply And.intro
                  exact assump_80
                  exact assump_81
  case inr assump_17 =>
    cases assump_14
    case inl assump_88 =>
      cases assump_88
      case inl assump_90 =>
        apply Or.inl
        apply Or.inr
        intro assump_94
        apply True.intro
      case inr assump_91 =>
        apply Or.inl
        apply Or.inr
        intro assump_97
        apply True.intro
    case inr assump_89 =>
      cases assump_89
      case intro assump_98 assump_99 =>
        cases assump_99
        case intro assump_102 assump_103 =>
          cases assump_103
          case intro assump_106 assump_107 =>
            apply Or.inl
            apply Or.inl
            apply And.intro
            exact assump_106
            exact assump_107


variable (p6 p7 p1 p0 p5 p4 : Prop)
theorem file48_21150 : ((((((p4 ∨ p4) ∧ (p7 ∧ p5)) → ((p0 → p6) → (p1 ∧ p7))) → (((p4 ∨ False) ∨ (p5 ∨ False)) → False)) ∧ ((((p5 → p0) → False) → ((p1 ∧ p7) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 → p0) → False) → ((p1 ∧ p7) → (False → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p2 p1 p4 p3 p6 : Prop)
theorem file48_21703 : ((((((p4 ∨ True) → False) → False) ∧ (((p2 ∧ False) → (False ∨ p6)) ∨ ((p1 → p6) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∨ True) → False) → False) ∧ (((p2 ∧ False) → (False ∨ p6)) ∨ ((p1 → p6) ∨ (p3 → False)))) := by
    apply And.intro
    intro assump_5
    have assump_23 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
    apply Or.inl
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p5 p4 p7 p3 p0 : Prop)
theorem file48_22407 : ((((((p2 ∨ p0) ∧ (False → True)) ∨ ((p3 ∨ True) ∨ (p4 → False))) ∨ (((p5 ∧ p5) → (p2 ∧ p7)) ∨ ((p2 ∧ p0) → False))) → False) → False) := by
  intro assump_10
  have assump_17 : ((((p2 ∨ p0) ∧ (False → True)) ∨ ((p3 ∨ True) ∨ (p4 → False))) ∨ (((p5 ∧ p5) → (p2 ∧ p7)) ∨ ((p2 ∧ p0) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_13 := assump_10 assump_17
  apply False.elim assump_13


variable (p3 p5 p2 p0 p7 p1 p6 : Prop)
theorem file48_22924 : (((((p7 ∧ True) ∨ (p7 ∨ False)) ∨ ((p3 ∨ p1) ∨ (p3 → False))) → (((False → False) → (False ∧ p0)) ∧ ((p2 → p5) ∧ (p7 → False)))) → ((((p6 → False) ∧ (p6 → False)) ∧ ((False ∧ p5) → (True → p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_39 : (((p7 ∧ True) ∨ (p7 ∨ False)) ∨ ((p3 ∨ p1) ∨ (p3 → False))) := by
        apply Or.inr
        apply Or.inr
        intro assump_16
        have assump_40 : (((p7 ∧ True) ∨ (p7 ∨ False)) ∨ ((p3 ∨ p1) ∨ (p3 → False))) := by
          apply Or.inr
          apply Or.inl
          apply Or.inl
          exact assump_16
        let assump_20 := assump_1 assump_40
        let assump_21 := And.left assump_20
        have assump_41 : (False → False) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_21 assump_41
        let assump_26 := And.left assump_22
        apply False.elim assump_26
      let assump_15 := assump_1 assump_39
      let assump_30 := And.left assump_15
      have assump_42 : (False → False) := by
        intro assump_32
        apply False.elim assump_32
      let assump_31 := assump_30 assump_42
      let assump_35 := And.left assump_31
      apply False.elim assump_35


variable (p4 p3 p5 p2 p0 : Prop)
theorem file48_24301 : ((((((False → p0) ∨ (False ∧ True)) ∨ ((p4 → p2) ∨ (p5 ∨ p4))) ∨ (((p2 → False) ∧ (p4 ∧ p2)) ∧ ((True ∧ False) ∧ (p4 ∨ p3)))) → False) → False) := by
  intro assump_5
  have assump_15 : ((((False → p0) ∨ (False ∧ True)) ∨ ((p4 → p2) ∨ (p5 ∨ p4))) ∨ (((p2 → False) ∧ (p4 ∧ p2)) ∧ ((True ∧ False) ∧ (p4 ∨ p3)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p2 p3 p6 p7 p0 p4 : Prop)
theorem file48_24842 : (((((p7 ∧ False) → False) → False) → (((p7 → False) ∨ (p7 → False)) → False)) ∨ ((((p3 ∨ p6) → (p2 → False)) → False) ∨ (((p4 → False) ∨ (p0 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_35 : ((p7 ∧ False) → False) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    let assump_9 := assump_1 assump_35
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_36 : ((p7 ∧ False) → False) := by
      intro assump_25
      cases assump_25
      case intro assump_26 assump_27 =>
        apply False.elim assump_27
    let assump_24 := assump_1 assump_36
    apply False.elim assump_24


variable (p1 p6 p3 p2 p0 : Prop)
theorem file48_25654 : (((((True ∨ False) → False) ∧ ((p1 → True) → False)) ∧ (((False ∧ p1) ∨ (p3 ∧ p6)) → ((True ∨ p2) → (p0 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_18 : (p1 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_18
      apply False.elim assump_13


variable (p1 p2 p0 p4 p6 p5 p3 p7 : Prop)
theorem file48_26139 : (((((True ∧ p5) ∨ (False → False)) → ((p4 ∧ False) → (p0 → p3))) ∨ (((p7 ∧ p3) → (True ∧ p1)) ∧ ((p6 → p2) → (p6 ∧ p3)))) ∨ ((((p6 → p5) ∨ (p2 → p5)) ∧ ((True → p1) → (p2 → False))) ∧ (((p4 → False) → False) ∧ ((p3 → p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p1 p5 p3 p7 p4 : Prop)
theorem file48_26597 : (((((p3 → False) → (p1 ∨ p5)) → ((False → False) → (p7 ∧ p3))) → (((p3 → True) ∧ (True ∨ p4)) → ((p3 → False) → False))) → ((((p1 ∨ True) → False) → False) ∨ (((True → p1) ∨ (p7 → False)) ∨ ((True ∧ True) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_11 : (p1 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p2 p0 p7 p5 p6 p1 p4 : Prop)
theorem file48_27072 : (((((p7 ∨ p6) → False) → False) → False) → ((((p1 ∧ p4) ∧ (p2 ∨ True)) ∧ ((True → False) → (p0 ∧ p4))) → (((p5 ∧ p7) → False) ∨ ((p1 → False) ∧ (p2 → p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          apply Or.inl
          intro assump_21
          cases assump_21
          case intro assump_22 assump_23 =>
            have assump_67 : (((p7 ∨ p6) → False) → False) := by
              intro assump_31
              have assump_68 : (p7 ∨ p6) := by
                apply Or.inl
                exact assump_23
              let assump_34 := assump_31 assump_68
              apply False.elim assump_34
            let assump_30 := assump_1 assump_67
            apply False.elim assump_30
        case inr assump_14 =>
          apply Or.inl
          intro assump_47
          cases assump_47
          case intro assump_48 assump_49 =>
            have assump_69 : (((p7 ∨ p6) → False) → False) := by
              intro assump_57
              have assump_70 : (p7 ∨ p6) := by
                apply Or.inl
                exact assump_49
              let assump_60 := assump_57 assump_70
              apply False.elim assump_60
            let assump_56 := assump_1 assump_69
            apply False.elim assump_56


variable (p1 : Prop)
theorem file48_28565 : ((((((False ∧ p1) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p1) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p1) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p2 p0 p5 p4 p3 p7 p6 : Prop)
theorem file48_29105 : (((((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) → False) → ((((p6 ∧ p6) ∧ (p6 ∨ p7)) ∧ ((p1 ∨ p2) ∧ (p0 ∧ p1))) → (((p7 → p4) ∨ (p3 ∨ p5)) ∧ ((p3 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          cases assump_4
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_18
              case intro assump_23 assump_24 =>
                apply Or.inl
                intro assump_31
                have assump_182 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inr
                  apply True.intro
                  apply Or.inr
                  exact assump_23
                let assump_35 := assump_1 assump_182
                apply False.elim assump_35
            case inr assump_20 =>
              cases assump_18
              case intro assump_41 assump_42 =>
                apply Or.inl
                intro assump_49
                have assump_183 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_20
                  apply Or.inr
                  exact assump_41
                let assump_53 := assump_1 assump_183
                apply False.elim assump_53
        case inr assump_14 =>
          cases assump_4
          case intro assump_59 assump_60 =>
            cases assump_59
            case inl assump_61 =>
              cases assump_60
              case intro assump_65 assump_66 =>
                apply Or.inl
                intro assump_73
                have assump_184 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inr
                  apply True.intro
                  apply Or.inr
                  exact assump_65
                let assump_77 := assump_1 assump_184
                apply False.elim assump_77
            case inr assump_62 =>
              cases assump_60
              case intro assump_83 assump_84 =>
                apply Or.inl
                intro assump_91
                have assump_185 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_62
                  apply Or.inr
                  exact assump_83
                let assump_95 := assump_1 assump_185
                apply False.elim assump_95
  intro assump_99
  cases assump_2
  case intro assump_102 assump_103 =>
    cases assump_102
    case intro assump_104 assump_105 =>
      cases assump_104
      case intro assump_106 assump_107 =>
        cases assump_105
        case inl assump_112 =>
          cases assump_103
          case intro assump_116 assump_117 =>
            cases assump_116
            case inl assump_118 =>
              cases assump_117
              case intro assump_122 assump_123 =>
                have assump_186 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inr
                  apply True.intro
                  apply Or.inr
                  exact assump_122
                let assump_130 := assump_1 assump_186
                apply False.elim assump_130
            case inr assump_119 =>
              cases assump_117
              case intro assump_136 assump_137 =>
                have assump_187 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_119
                  apply Or.inr
                  exact assump_136
                let assump_144 := assump_1 assump_187
                apply False.elim assump_144
        case inr assump_113 =>
          cases assump_103
          case intro assump_150 assump_151 =>
            cases assump_150
            case inl assump_152 =>
              cases assump_151
              case intro assump_156 assump_157 =>
                have assump_188 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inr
                  apply True.intro
                  apply Or.inr
                  exact assump_156
                let assump_164 := assump_1 assump_188
                apply False.elim assump_164
            case inr assump_153 =>
              cases assump_151
              case intro assump_170 assump_171 =>
                have assump_189 : (((p2 ∨ True) ∧ (p3 ∨ p0)) ∨ ((p6 ∧ p2) ∧ (p1 ∨ p5))) := by
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_153
                  apply Or.inr
                  exact assump_170
                let assump_178 := assump_1 assump_189
                apply False.elim assump_178


variable (p2 p1 p4 p6 p0 p5 p7 p3 : Prop)
theorem file48_34590 : ((((((p2 ∨ p5) → False) ∧ ((p3 ∧ True) → (p6 → False))) ∧ (((p7 ∨ p5) → (p5 → p0)) → False)) ∧ ((((p6 → False) ∧ (p1 ∨ p2)) → ((p4 → p2) → (p3 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_23 : (((p6 → False) ∧ (p1 ∨ p2)) → ((p4 → p2) → (p3 → True))) := by
          intro assump_17
          intro assump_18
          intro assump_19
          apply True.intro
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p2 p4 p1 p5 p0 p7 p3 : Prop)
theorem file48_35285 : (((((p2 → p2) → False) ∨ ((p3 ∨ p5) ∨ (p0 → False))) ∧ (((p0 → True) ∨ (p1 ∨ False)) ∧ ((p0 ∧ True) ∧ (False ∧ p3)))) → ((((p4 → False) → (p2 → p4)) ∨ ((p3 ∧ p7) ∨ (p2 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_14
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                cases assump_20
                case intro assump_27 assump_28 =>
                  apply False.elim assump_27
          case inr assump_16 =>
            cases assump_16
            case inl assump_31 =>
              cases assump_14
              case intro assump_35 assump_36 =>
                cases assump_35
                case intro assump_37 assump_38 =>
                  cases assump_36
                  case intro assump_43 assump_44 =>
                    apply False.elim assump_43
            case inr assump_32 =>
              apply False.elim assump_32
      case inr assump_10 =>
        cases assump_10
        case inl assump_49 =>
          cases assump_49
          case inl assump_51 =>
            cases assump_8
            case intro assump_55 assump_56 =>
              cases assump_55
              case inl assump_57 =>
                cases assump_56
                case intro assump_61 assump_62 =>
                  cases assump_61
                  case intro assump_63 assump_64 =>
                    cases assump_62
                    case intro assump_69 assump_70 =>
                      apply False.elim assump_69
              case inr assump_58 =>
                cases assump_58
                case inl assump_73 =>
                  cases assump_56
                  case intro assump_77 assump_78 =>
                    cases assump_77
                    case intro assump_79 assump_80 =>
                      cases assump_78
                      case intro assump_85 assump_86 =>
                        apply False.elim assump_85
                case inr assump_74 =>
                  apply False.elim assump_74
          case inr assump_52 =>
            cases assump_8
            case intro assump_93 assump_94 =>
              cases assump_93
              case inl assump_95 =>
                cases assump_94
                case intro assump_99 assump_100 =>
                  cases assump_99
                  case intro assump_101 assump_102 =>
                    cases assump_100
                    case intro assump_107 assump_108 =>
                      apply False.elim assump_107
              case inr assump_96 =>
                cases assump_96
                case inl assump_111 =>
                  cases assump_94
                  case intro assump_115 assump_116 =>
                    cases assump_115
                    case intro assump_117 assump_118 =>
                      cases assump_116
                      case intro assump_123 assump_124 =>
                        apply False.elim assump_123
                case inr assump_112 =>
                  apply False.elim assump_112
        case inr assump_50 =>
          cases assump_8
          case intro assump_131 assump_132 =>
            cases assump_131
            case inl assump_133 =>
              cases assump_132
              case intro assump_137 assump_138 =>
                cases assump_137
                case intro assump_139 assump_140 =>
                  cases assump_138
                  case intro assump_145 assump_146 =>
                    apply False.elim assump_145
            case inr assump_134 =>
              cases assump_134
              case inl assump_149 =>
                cases assump_132
                case intro assump_153 assump_154 =>
                  cases assump_153
                  case intro assump_155 assump_156 =>
                    cases assump_154
                    case intro assump_161 assump_162 =>
                      apply False.elim assump_161
              case inr assump_150 =>
                apply False.elim assump_150
  case inr assump_4 =>
    cases assump_4
    case inl assump_167 =>
      cases assump_167
      case intro assump_169 assump_170 =>
        cases assump_1
        case intro assump_175 assump_176 =>
          cases assump_175
          case inl assump_177 =>
            cases assump_176
            case intro assump_181 assump_182 =>
              cases assump_181
              case inl assump_183 =>
                cases assump_182
                case intro assump_187 assump_188 =>
                  cases assump_187
                  case intro assump_189 assump_190 =>
                    cases assump_188
                    case intro assump_195 assump_196 =>
                      apply False.elim assump_195
              case inr assump_184 =>
                cases assump_184
                case inl assump_199 =>
                  cases assump_182
                  case intro assump_203 assump_204 =>
                    cases assump_203
                    case intro assump_205 assump_206 =>
                      cases assump_204
                      case intro assump_211 assump_212 =>
                        apply False.elim assump_211
                case inr assump_200 =>
                  apply False.elim assump_200
          case inr assump_178 =>
            cases assump_178
            case inl assump_217 =>
              cases assump_217
              case inl assump_219 =>
                cases assump_176
                case intro assump_223 assump_224 =>
                  cases assump_223
                  case inl assump_225 =>
                    cases assump_224
                    case intro assump_229 assump_230 =>
                      cases assump_229
                      case intro assump_231 assump_232 =>
                        cases assump_230
                        case intro assump_237 assump_238 =>
                          apply False.elim assump_237
                  case inr assump_226 =>
                    cases assump_226
                    case inl assump_241 =>
                      cases assump_224
                      case intro assump_245 assump_246 =>
                        cases assump_245
                        case intro assump_247 assump_248 =>
                          cases assump_246
                          case intro assump_253 assump_254 =>
                            apply False.elim assump_253
                    case inr assump_242 =>
                      apply False.elim assump_242
              case inr assump_220 =>
                cases assump_176
                case intro assump_261 assump_262 =>
                  cases assump_261
                  case inl assump_263 =>
                    cases assump_262
                    case intro assump_267 assump_268 =>
                      cases assump_267
                      case intro assump_269 assump_270 =>
                        cases assump_268
                        case intro assump_275 assump_276 =>
                          apply False.elim assump_275
                  case inr assump_264 =>
                    cases assump_264
                    case inl assump_279 =>
                      cases assump_262
                      case intro assump_283 assump_284 =>
                        cases assump_283
                        case intro assump_285 assump_286 =>
                          cases assump_284
                          case intro assump_291 assump_292 =>
                            apply False.elim assump_291
                    case inr assump_280 =>
                      apply False.elim assump_280
            case inr assump_218 =>
              cases assump_176
              case intro assump_299 assump_300 =>
                cases assump_299
                case inl assump_301 =>
                  cases assump_300
                  case intro assump_305 assump_306 =>
                    cases assump_305
                    case intro assump_307 assump_308 =>
                      cases assump_306
                      case intro assump_313 assump_314 =>
                        apply False.elim assump_313
                case inr assump_302 =>
                  cases assump_302
                  case inl assump_317 =>
                    cases assump_300
                    case intro assump_321 assump_322 =>
                      cases assump_321
                      case intro assump_323 assump_324 =>
                        cases assump_322
                        case intro assump_329 assump_330 =>
                          apply False.elim assump_329
                  case inr assump_318 =>
                    apply False.elim assump_318
    case inr assump_168 =>
      cases assump_1
      case intro assump_337 assump_338 =>
        cases assump_337
        case inl assump_339 =>
          cases assump_338
          case intro assump_343 assump_344 =>
            cases assump_343
            case inl assump_345 =>
              cases assump_344
              case intro assump_349 assump_350 =>
                cases assump_349
                case intro assump_351 assump_352 =>
                  cases assump_350
                  case intro assump_357 assump_358 =>
                    apply False.elim assump_357
            case inr assump_346 =>
              cases assump_346
              case inl assump_361 =>
                cases assump_344
                case intro assump_365 assump_366 =>
                  cases assump_365
                  case intro assump_367 assump_368 =>
                    cases assump_366
                    case intro assump_373 assump_374 =>
                      apply False.elim assump_373
              case inr assump_362 =>
                apply False.elim assump_362
        case inr assump_340 =>
          cases assump_340
          case inl assump_379 =>
            cases assump_379
            case inl assump_381 =>
              cases assump_338
              case intro assump_385 assump_386 =>
                cases assump_385
                case inl assump_387 =>
                  cases assump_386
                  case intro assump_391 assump_392 =>
                    cases assump_391
                    case intro assump_393 assump_394 =>
                      cases assump_392
                      case intro assump_399 assump_400 =>
                        apply False.elim assump_399
                case inr assump_388 =>
                  cases assump_388
                  case inl assump_403 =>
                    cases assump_386
                    case intro assump_407 assump_408 =>
                      cases assump_407
                      case intro assump_409 assump_410 =>
                        cases assump_408
                        case intro assump_415 assump_416 =>
                          apply False.elim assump_415
                  case inr assump_404 =>
                    apply False.elim assump_404
            case inr assump_382 =>
              cases assump_338
              case intro assump_423 assump_424 =>
                cases assump_423
                case inl assump_425 =>
                  cases assump_424
                  case intro assump_429 assump_430 =>
                    cases assump_429
                    case intro assump_431 assump_432 =>
                      cases assump_430
                      case intro assump_437 assump_438 =>
                        apply False.elim assump_437
                case inr assump_426 =>
                  cases assump_426
                  case inl assump_441 =>
                    cases assump_424
                    case intro assump_445 assump_446 =>
                      cases assump_445
                      case intro assump_447 assump_448 =>
                        cases assump_446
                        case intro assump_453 assump_454 =>
                          apply False.elim assump_453
                  case inr assump_442 =>
                    apply False.elim assump_442
          case inr assump_380 =>
            cases assump_338
            case intro assump_461 assump_462 =>
              cases assump_461
              case inl assump_463 =>
                cases assump_462
                case intro assump_467 assump_468 =>
                  cases assump_467
                  case intro assump_469 assump_470 =>
                    cases assump_468
                    case intro assump_475 assump_476 =>
                      apply False.elim assump_475
              case inr assump_464 =>
                cases assump_464
                case inl assump_479 =>
                  cases assump_462
                  case intro assump_483 assump_484 =>
                    cases assump_483
                    case intro assump_485 assump_486 =>
                      cases assump_484
                      case intro assump_491 assump_492 =>
                        apply False.elim assump_491
                case inr assump_480 =>
                  apply False.elim assump_480


variable (p1 p0 p4 p7 p5 p3 p2 p6 : Prop)
theorem file48_48698 : (((((True ∨ p4) ∧ (p1 → False)) → ((p1 ∧ p6) → (p0 ∨ p2))) ∨ (((p4 ∨ p2) → False) ∧ ((p5 ∨ p1) ∧ (False → False)))) ∨ ((((p2 ∨ p0) ∨ (p3 → False)) → ((p1 ∧ p7) → (p0 ∨ True))) ∧ (((p2 ∨ False) → False) → ((p4 ∧ p7) → (p3 → p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_7
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        have assump_35 : p1 := by
          exact assump_9
        let assump_23 := assump_16 assump_35
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_36 : p1 := by
          exact assump_9
        let assump_31 := assump_16 assump_36
        apply False.elim assump_31


variable (p4 p3 : Prop)
theorem file48_49512 : ((((((True → False) → False) → False) → (((p3 → False) ∨ (False ∧ p4)) ∨ ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True → False) → False) → False) → (((p3 → False) ∨ (False ∧ p4)) ∨ ((p4 → False) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_27 : ((True → False) → False) := by
      intro assump_13
      have assump_28 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_28
      apply False.elim assump_16
    let assump_12 := assump_5 assump_27
    apply False.elim assump_12
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p4 p3 p5 p7 p2 p0 p1 : Prop)
theorem file48_50255 : (((((False → False) ∧ (True ∨ p6)) ∨ ((True ∨ p7) ∨ (p4 ∧ p5))) ∨ (((p2 ∧ p4) ∨ (p2 → False)) → ((p6 → p0) ∨ (p4 → p4)))) ∨ ((((p3 → False) ∧ (p6 ∧ p1)) → ((p2 ∧ p1) ∧ (p1 ∨ p0))) ∨ (((p6 ∨ p4) ∨ (p5 → p6)) → ((p7 ∨ p0) → (True ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  apply False.elim assump_1
  apply Or.inl
  apply True.intro


variable (p6 p2 p0 p4 p7 p3 p1 : Prop)
theorem file48_50706 : (((((p3 → False) → False) ∧ ((p2 ∧ True) → (p7 ∨ p4))) ∧ (((p3 ∧ p1) → False) → ((p0 → False) → False))) → ((((p2 ∧ p6) ∨ (p4 → p7)) → ((False → False) ∨ (p4 ∧ p4))) ∨ (((False ∧ p2) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
      case inr assump_14 =>
        apply Or.inl
        intro assump_26
        apply False.elim assump_26


variable (p7 p6 p0 p3 p1 p2 p5 : Prop)
theorem file48_51452 : (((((p7 ∧ p3) ∧ (p3 → False)) → False) → False) → ((((p7 ∨ p1) → False) ∨ ((p5 → False) ∨ (p1 ∧ p7))) → (((p6 ∨ p2) ∧ (p5 ∧ p0)) ∧ ((p3 → p1) → (p2 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    have assump_374 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_375 : p3 := by
            exact assump_14
          let assump_21 := assump_12 assump_375
          apply False.elim assump_21
    let assump_9 := assump_1 assump_374
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_28 =>
      have assump_376 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_35
        cases assump_35
        case intro assump_36 assump_37 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            have assump_377 : p3 := by
              exact assump_39
            let assump_46 := assump_37 assump_377
            apply False.elim assump_46
      let assump_34 := assump_1 assump_376
      apply False.elim assump_34
    case inr assump_29 =>
      cases assump_29
      case intro assump_53 assump_54 =>
        have assump_378 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
          intro assump_62
          cases assump_62
          case intro assump_63 assump_64 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              have assump_379 : p3 := by
                exact assump_66
              let assump_73 := assump_64 assump_379
              apply False.elim assump_73
        let assump_61 := assump_1 assump_378
        apply False.elim assump_61
  apply And.intro
  cases assump_2
  case inl assump_80 =>
    have assump_380 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_87
      cases assump_87
      case intro assump_88 assump_89 =>
        cases assump_88
        case intro assump_90 assump_91 =>
          have assump_381 : p3 := by
            exact assump_91
          let assump_98 := assump_89 assump_381
          apply False.elim assump_98
    let assump_86 := assump_1 assump_380
    apply False.elim assump_86
  case inr assump_81 =>
    cases assump_81
    case inl assump_105 =>
      have assump_382 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_112
        cases assump_112
        case intro assump_113 assump_114 =>
          cases assump_113
          case intro assump_115 assump_116 =>
            have assump_383 : p3 := by
              exact assump_116
            let assump_123 := assump_114 assump_383
            apply False.elim assump_123
      let assump_111 := assump_1 assump_382
      apply False.elim assump_111
    case inr assump_106 =>
      cases assump_106
      case intro assump_130 assump_131 =>
        have assump_384 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
          intro assump_139
          cases assump_139
          case intro assump_140 assump_141 =>
            cases assump_140
            case intro assump_142 assump_143 =>
              have assump_385 : p3 := by
                exact assump_143
              let assump_150 := assump_141 assump_385
              apply False.elim assump_150
        let assump_138 := assump_1 assump_384
        apply False.elim assump_138
  cases assump_2
  case inl assump_157 =>
    have assump_386 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_164
      cases assump_164
      case intro assump_165 assump_166 =>
        cases assump_165
        case intro assump_167 assump_168 =>
          have assump_387 : p3 := by
            exact assump_168
          let assump_175 := assump_166 assump_387
          apply False.elim assump_175
    let assump_163 := assump_1 assump_386
    apply False.elim assump_163
  case inr assump_158 =>
    cases assump_158
    case inl assump_182 =>
      have assump_388 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_189
        cases assump_189
        case intro assump_190 assump_191 =>
          cases assump_190
          case intro assump_192 assump_193 =>
            have assump_389 : p3 := by
              exact assump_193
            let assump_200 := assump_191 assump_389
            apply False.elim assump_200
      let assump_188 := assump_1 assump_388
      apply False.elim assump_188
    case inr assump_183 =>
      cases assump_183
      case intro assump_207 assump_208 =>
        have assump_390 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
          intro assump_216
          cases assump_216
          case intro assump_217 assump_218 =>
            cases assump_217
            case intro assump_219 assump_220 =>
              have assump_391 : p3 := by
                exact assump_220
              let assump_227 := assump_218 assump_391
              apply False.elim assump_227
        let assump_215 := assump_1 assump_390
        apply False.elim assump_215
  intro assump_234
  apply And.intro
  cases assump_2
  case inl assump_237 =>
    have assump_392 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_244
      cases assump_244
      case intro assump_245 assump_246 =>
        cases assump_245
        case intro assump_247 assump_248 =>
          have assump_393 : p3 := by
            exact assump_248
          let assump_255 := assump_246 assump_393
          apply False.elim assump_255
    let assump_243 := assump_1 assump_392
    apply False.elim assump_243
  case inr assump_238 =>
    cases assump_238
    case inl assump_262 =>
      have assump_394 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_269
        cases assump_269
        case intro assump_270 assump_271 =>
          cases assump_270
          case intro assump_272 assump_273 =>
            have assump_395 : p3 := by
              exact assump_273
            let assump_280 := assump_271 assump_395
            apply False.elim assump_280
      let assump_268 := assump_1 assump_394
      apply False.elim assump_268
    case inr assump_263 =>
      cases assump_263
      case intro assump_287 assump_288 =>
        have assump_396 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
          intro assump_296
          cases assump_296
          case intro assump_297 assump_298 =>
            cases assump_297
            case intro assump_299 assump_300 =>
              have assump_397 : p3 := by
                exact assump_300
              let assump_307 := assump_298 assump_397
              apply False.elim assump_307
        let assump_295 := assump_1 assump_396
        apply False.elim assump_295
  cases assump_2
  case inl assump_316 =>
    have assump_398 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
      intro assump_323
      cases assump_323
      case intro assump_324 assump_325 =>
        cases assump_324
        case intro assump_326 assump_327 =>
          have assump_399 : p3 := by
            exact assump_327
          let assump_334 := assump_325 assump_399
          apply False.elim assump_334
    let assump_322 := assump_1 assump_398
    apply False.elim assump_322
  case inr assump_317 =>
    cases assump_317
    case inl assump_341 =>
      have assump_400 : (((p7 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_348
        cases assump_348
        case intro assump_349 assump_350 =>
          cases assump_349
          case intro assump_351 assump_352 =>
            have assump_401 : p3 := by
              exact assump_352
            let assump_359 := assump_350 assump_401
            apply False.elim assump_359
      let assump_347 := assump_1 assump_400
      apply False.elim assump_347
    case inr assump_342 =>
      cases assump_342
      case intro assump_366 assump_367 =>
        exact assump_367


variable (p5 p2 p7 p6 p3 p0 p1 p4 : Prop)
theorem file48_59411 : ((((((True ∨ p3) ∨ (p7 → False)) → ((True ∨ p7) → False)) ∧ (((p4 ∨ p3) ∨ (p0 → False)) ∨ ((p2 ∨ False) → (p0 ∧ p4)))) ∨ ((((p6 ∧ p3) ∧ (p5 → False)) ∨ ((p1 → p3) ∧ (p0 ∨ True))) ∧ (((p1 ∨ False) → (False → False)) → ((p2 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            have assump_106 : ((True ∨ p3) ∨ (p7 → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_17 := assump_4 assump_106
            have assump_107 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_18 := assump_17 assump_107
            apply False.elim assump_18
          case inr assump_13 =>
            have assump_108 : ((True ∨ p3) ∨ (p7 → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_25 := assump_4 assump_108
            have assump_109 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_26 := assump_25 assump_109
            apply False.elim assump_26
        case inr assump_11 =>
          have assump_110 : ((True ∨ p3) ∨ (p7 → False)) := by
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_33 := assump_4 assump_110
          have assump_111 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_34 := assump_33 assump_111
          apply False.elim assump_34
      case inr assump_9 =>
        have assump_112 : ((True ∨ p3) ∨ (p7 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_41 := assump_4 assump_112
        have assump_113 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_42 := assump_41 assump_113
        apply False.elim assump_42
  case inr assump_3 =>
    cases assump_3
    case intro assump_46 assump_47 =>
      cases assump_46
      case inl assump_48 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            have assump_114 : ((p1 ∨ False) → (False → False)) := by
              intro assump_63
              intro assump_64
              apply False.elim assump_64
            let assump_62 := assump_47 assump_114
            have assump_115 : (p2 → True) := by
              intro assump_68
              apply True.intro
            let assump_67 := assump_62 assump_115
            apply False.elim assump_67
      case inr assump_49 =>
        cases assump_49
        case intro assump_72 assump_73 =>
          cases assump_73
          case inl assump_76 =>
            have assump_116 : ((p1 ∨ False) → (False → False)) := by
              intro assump_83
              intro assump_84
              apply False.elim assump_84
            let assump_82 := assump_47 assump_116
            have assump_117 : (p2 → True) := by
              intro assump_88
              apply True.intro
            let assump_87 := assump_82 assump_117
            apply False.elim assump_87
          case inr assump_77 =>
            have assump_118 : ((p1 ∨ False) → (False → False)) := by
              intro assump_97
              intro assump_98
              apply False.elim assump_98
            let assump_96 := assump_47 assump_118
            have assump_119 : (p2 → True) := by
              intro assump_102
              apply True.intro
            let assump_101 := assump_96 assump_119
            apply False.elim assump_101


variable (p6 p7 p1 p0 p5 p4 : Prop)
theorem file48_63311 : (((((p0 → p7) → False) → ((p6 → p1) ∧ (True → False))) ∧ (((True → False) → False) → False)) → ((((p0 ∨ p4) → False) ∨ ((True → False) → (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      have assump_43 : ((True → False) → False) := by
        intro assump_14
        have assump_44 : True := by
          apply True.intro
        let assump_17 := assump_14 assump_44
        apply False.elim assump_17
      let assump_13 := assump_8 assump_43
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      have assump_45 : ((True → False) → False) := by
        intro assump_33
        have assump_46 : True := by
          apply True.intro
        let assump_36 := assump_33 assump_46
        apply False.elim assump_36
      let assump_32 := assump_27 assump_45
      apply False.elim assump_32


variable (p4 p3 p5 p1 p7 p6 : Prop)
theorem file48_64341 : ((((((False ∨ p1) ∧ (p7 → False)) → False) → (((p5 ∧ True) ∨ (p3 → p1)) → False)) ∧ ((((False ∧ p3) ∨ (True → False)) → ((False ∧ p4) → (p6 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((False ∧ p3) ∨ (True → False)) → ((False ∧ p4) → (p6 → p1))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p2 p4 p5 p7 p0 p3 : Prop)
theorem file48_64963 : ((((((p2 ∧ p2) ∨ (True → False)) → False) ∧ (((p7 ∨ p7) ∧ (p3 ∨ p4)) ∨ ((p3 ∨ p5) ∧ (p2 → p0)))) ∧ ((((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case inl assump_16 =>
              have assump_96 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_23
                apply False.elim assump_23
              let assump_22 := assump_3 assump_96
              apply False.elim assump_22
            case inr assump_17 =>
              have assump_97 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_3 assump_97
              apply False.elim assump_33
          case inr assump_13 =>
            cases assump_11
            case inl assump_42 =>
              have assump_98 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_49
                apply False.elim assump_49
              let assump_48 := assump_3 assump_98
              apply False.elim assump_48
            case inr assump_43 =>
              have assump_99 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_60
                apply False.elim assump_60
              let assump_59 := assump_3 assump_99
              apply False.elim assump_59
      case inr assump_9 =>
        cases assump_9
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            have assump_100 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
              apply Or.inl
              apply Or.inl
              intro assump_77
              apply False.elim assump_77
            let assump_76 := assump_3 assump_100
            apply False.elim assump_76
          case inr assump_69 =>
            have assump_101 : (((False → False) ∨ (True → p0)) ∨ ((p5 → p4) → (p7 → False))) := by
              apply Or.inl
              apply Or.inl
              intro assump_90
              apply False.elim assump_90
            let assump_89 := assump_3 assump_101
            apply False.elim assump_89


variable (p5 p4 p0 p7 p1 : Prop)
theorem file48_67828 : (((((True ∧ False) → (p5 ∧ p1)) ∨ ((p1 → p7) → (p5 ∧ p7))) → False) → ((((True ∧ p5) ∨ (p0 ∧ p4)) ∧ ((False ∨ p7) → False)) ∨ (((False ∨ p5) ∧ (True → False)) ∧ ((p7 → True) ∨ (True ∧ False))))) := by
  intro assump_22
  have assump_42 : (((True ∧ False) → (p5 ∧ p1)) ∨ ((p1 → p7) → (p5 ∧ p7))) := by
    apply Or.inl
    intro assump_26
    apply And.intro
    cases assump_26
    case intro assump_27 assump_28 =>
      apply False.elim assump_28
    cases assump_26
    case intro assump_33 assump_34 =>
      apply False.elim assump_34
  let assump_25 := assump_22 assump_42
  apply False.elim assump_25


variable (p1 p6 p4 p0 : Prop)
theorem file48_68490 : (((((p4 ∧ p1) → (False → False)) ∨ ((p6 ∨ p4) → False)) → False) → ((((p0 → False) ∨ (True ∧ True)) → False) → (((p6 → False) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_18 : (((p4 ∧ p1) → (False → False)) ∨ ((p6 ∨ p4) → False)) := by
    apply Or.inl
    intro assump_11
    intro assump_12
    apply False.elim assump_12
  let assump_10 := assump_1 assump_18
  apply False.elim assump_10


variable (p5 p2 p6 p4 p3 p7 : Prop)
theorem file48_68987 : (((((p6 → False) ∧ (p3 ∨ p7)) ∨ ((True ∧ False) → False)) → False) → ((((p7 ∧ True) ∧ (p5 ∨ p6)) ∨ ((p4 → False) → (p3 ∨ p2))) → (((p2 → p2) ∨ (p2 → False)) ∨ ((False → p6) → (p2 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_19
          exact assump_19
        case inr assump_14 =>
          apply Or.inl
          apply Or.inl
          intro assump_26
          exact assump_26
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    intro assump_33
    exact assump_33


variable (p7 p3 p0 p1 p6 p2 p4 p5 : Prop)
theorem file48_69815 : (((((p4 → True) ∧ (p5 → p5)) ∨ ((True ∨ True) ∧ (p3 → p2))) ∨ (((p1 → True) → (False ∨ p4)) → False)) ∨ ((((p7 ∨ True) → False) → ((p0 ∨ p6) → False)) ∨ (((p1 → p0) → False) ∨ ((p1 → False) → (p6 → p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_5
  apply True.intro
  intro assump_6
  exact assump_6


variable (p4 p3 p7 : Prop)
theorem file48_70211 : ((((((True → False) ∧ (p7 → False)) → False) → False) ∨ ((((True → False) ∧ (True ∨ p7)) → False) ∧ (((True → False) → (p4 ∨ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_39 : (((True → False) ∧ (p7 → False)) → False) := by
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        have assump_40 : True := by
          apply True.intro
        let assump_15 := assump_8 assump_40
        apply False.elim assump_15
    let assump_6 := assump_2 assump_39
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_22 assump_23 =>
      have assump_41 : ((True → False) → (p4 ∨ p3)) := by
        intro assump_29
        have assump_42 : True := by
          apply True.intro
        let assump_32 := assump_29 assump_42
        apply False.elim assump_32
      let assump_28 := assump_23 assump_41
      apply False.elim assump_28


variable (p3 p6 p1 p4 p2 p0 p5 p7 : Prop)
theorem file48_71231 : (((((True ∨ p3) → False) → ((p3 → False) → (p0 → p6))) ∨ (((p4 → True) → (p0 ∧ p2)) ∧ ((p4 ∧ p5) → False))) ∨ ((((p7 → False) → False) → ((p1 ∧ True) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_14 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_14
  apply False.elim assump_10


variable (p7 p3 p6 p1 p5 : Prop)
theorem file48_71687 : ((((((p1 → p5) → False) → False) ∧ (((False ∨ True) ∧ (p6 → False)) → False)) ∧ ((((p7 → True) ∨ (p7 ∧ p1)) ∧ ((False → p1) ∨ (p3 ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_20 : (((p7 → True) ∨ (p7 ∧ p1)) ∧ ((False → p1) ∨ (p3 ∨ p7))) := by
        apply And.intro
        apply Or.inl
        intro assump_13
        apply True.intro
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      let assump_12 := assump_3 assump_20
      apply False.elim assump_12


variable (p3 : Prop)
theorem file48_72353 : (((((True → False) ∧ (p3 → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : (((True → False) ∧ (p3 → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p5 p6 p0 p1 p4 p2 p7 : Prop)
theorem file48_72844 : ((((((p3 ∨ p4) → (p6 → False)) → False) → (((p2 ∧ p1) ∨ (False → p3)) → ((p3 → False) ∧ (p3 ∧ p1)))) ∧ ((((p6 ∨ p3) ∨ (p0 ∧ p3)) → ((p4 → False) → (p2 → p0))) ∧ (((p5 → p7) → (p5 → p0)) ∧ ((p4 → False) ∧ (p4 ∧ True))))) → False) := by
  intro assump_72
  cases assump_72
  case intro assump_73 assump_74 =>
    cases assump_74
    case intro assump_77 assump_78 =>
      cases assump_78
      case intro assump_81 assump_82 =>
        cases assump_82
        case intro assump_85 assump_86 =>
          cases assump_86
          case intro assump_89 assump_90 =>
            have assump_100 : p4 := by
              exact assump_89
            let assump_96 := assump_85 assump_100
            apply False.elim assump_96


variable (p7 p0 p4 p1 p3 p2 p5 : Prop)
theorem file48_73628 : (((((p0 → p1) ∨ (p5 ∨ p3)) ∧ ((p1 → False) ∧ (p1 ∨ p1))) → (((True → p3) → (p3 → False)) ∨ ((p0 → p7) → False))) ∨ ((((p1 → False) ∧ (p1 → p4)) → False) ∨ (((p4 ∨ p2) ∨ (p0 → False)) ∨ ((True ∧ False) → (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          have assump_128 : p1 := by
            exact assump_12
          let assump_26 := assump_8 assump_128
          apply False.elim assump_26
        case inr assump_13 =>
          apply Or.inl
          intro assump_32
          intro assump_33
          have assump_129 : p1 := by
            exact assump_13
          let assump_42 := assump_8 assump_129
          apply False.elim assump_42
    case inr assump_5 =>
      cases assump_5
      case inl assump_46 =>
        cases assump_3
        case intro assump_50 assump_51 =>
          cases assump_51
          case inl assump_54 =>
            apply Or.inl
            intro assump_58
            intro assump_59
            have assump_130 : p1 := by
              exact assump_54
            let assump_68 := assump_50 assump_130
            apply False.elim assump_68
          case inr assump_55 =>
            apply Or.inl
            intro assump_74
            intro assump_75
            have assump_131 : p1 := by
              exact assump_55
            let assump_84 := assump_50 assump_131
            apply False.elim assump_84
      case inr assump_47 =>
        cases assump_3
        case intro assump_90 assump_91 =>
          cases assump_91
          case inl assump_94 =>
            apply Or.inl
            intro assump_98
            intro assump_99
            have assump_132 : p1 := by
              exact assump_94
            let assump_108 := assump_90 assump_132
            apply False.elim assump_108
          case inr assump_95 =>
            apply Or.inl
            intro assump_114
            intro assump_115
            have assump_133 : p1 := by
              exact assump_95
            let assump_124 := assump_90 assump_133
            apply False.elim assump_124


variable (p5 p6 p1 p0 p7 p3 p4 p2 : Prop)
theorem file48_76011 : (((((False → p4) → (False → False)) ∨ ((p6 → False) ∨ (p2 ∨ p3))) → (((p4 ∨ p1) ∨ (p4 → p0)) ∧ ((p1 ∨ p5) ∨ (p4 → False)))) → ((((True ∨ p2) ∨ (p7 ∧ p0)) ∨ ((p0 ∧ p0) → False)) ∨ (((p0 → False) → (p0 ∨ True)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p0 p2 p5 p6 p4 : Prop)
theorem file48_76390 : (((((p4 ∧ False) ∧ (p6 ∨ p0)) ∧ ((p5 → False) → (p2 → p5))) ∧ (((p2 → p6) → (p0 → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9


variable (p4 p6 p1 p5 p7 : Prop)
theorem file48_76840 : (((((True → p5) → (p6 → False)) → ((p1 → False) → (p5 → p4))) ∧ (((True → False) → (p5 → p6)) → False)) → ((((p7 → p6) → False) → False) → False)) := by
  intro assump_13
  intro assump_14
  cases assump_13
  case intro assump_17 assump_18 =>
    have assump_37 : ((True → False) → (p5 → p6)) := by
      intro assump_24
      intro assump_25
      have assump_38 : True := by
        apply True.intro
      let assump_30 := assump_24 assump_38
      apply False.elim assump_30
    let assump_23 := assump_18 assump_37
    apply False.elim assump_23


variable (p5 p0 p6 p1 : Prop)
theorem file48_77444 : ((((((p6 → False) ∨ (p0 → p1)) ∧ ((p5 → False) ∧ (p5 ∧ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p6 → False) ∨ (p0 → p1)) ∧ ((p5 → False) ∧ (p5 ∧ p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_50 : p5 := by
              exact assump_16
            let assump_24 := assump_12 assump_50
            apply False.elim assump_24
      case inr assump_9 =>
        cases assump_7
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            have assump_51 : p5 := by
              exact assump_34
            let assump_42 := assump_30 assump_51
            apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p5 p6 p4 p0 p7 p2 : Prop)
theorem file48_78504 : ((((((p0 ∨ p7) ∧ (p0 ∧ p4)) → ((p5 → p4) ∨ (False → True))) ∨ (((p2 → False) → (p6 → False)) → ((True → False) → (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p0 ∨ p7) ∧ (p0 ∧ p4)) → ((p5 → p4) ∨ (False → True))) ∨ (((p2 → False) → (p6 → False)) → ((True → False) → (p5 → p5)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          exact assump_13
      case inr assump_9 =>
        cases assump_7
        case intro assump_23 assump_24 =>
          apply Or.inl
          intro assump_29
          exact assump_24
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p7 p1 p4 p0 p5 p2 p6 : Prop)
theorem file48_79394 : ((((((p1 ∧ p6) ∧ (False ∧ p0)) ∨ ((p0 ∧ p7) → (p0 ∧ p0))) → False) ∧ ((((p0 ∨ p7) → (p6 → True)) → False) ∧ (((p6 → p2) ∨ (p1 → p6)) ∧ ((p4 ∨ p1) ∨ (p5 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              have assump_87 : ((p0 ∨ p7) → (p6 → True)) := by
                intro assump_25
                intro assump_26
                apply True.intro
              let assump_24 := assump_6 assump_87
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_88 : ((p0 ∨ p7) → (p6 → True)) := by
                intro assump_35
                intro assump_36
                apply True.intro
              let assump_34 := assump_6 assump_88
              apply False.elim assump_34
          case inr assump_17 =>
            have assump_89 : ((p0 ∨ p7) → (p6 → True)) := by
              intro assump_45
              intro assump_46
              apply True.intro
            let assump_44 := assump_6 assump_89
            apply False.elim assump_44
        case inr assump_13 =>
          cases assump_11
          case inl assump_52 =>
            cases assump_52
            case inl assump_54 =>
              have assump_90 : ((p0 ∨ p7) → (p6 → True)) := by
                intro assump_61
                intro assump_62
                apply True.intro
              let assump_60 := assump_6 assump_90
              apply False.elim assump_60
            case inr assump_55 =>
              have assump_91 : ((p0 ∨ p7) → (p6 → True)) := by
                intro assump_72
                intro assump_73
                apply True.intro
              let assump_71 := assump_6 assump_91
              apply False.elim assump_71
          case inr assump_53 =>
            have assump_92 : ((p0 ∨ p7) → (p6 → True)) := by
              intro assump_82
              intro assump_83
              apply True.intro
            let assump_81 := assump_6 assump_92
            apply False.elim assump_81


variable (p4 p1 p6 p7 p5 p3 p2 : Prop)
theorem file48_81759 : (((((p4 → p4) → False) → False) ∧ (((True ∧ p6) ∧ (p6 ∨ p4)) → ((p3 ∧ False) → (p3 → p1)))) ∨ ((((p7 → p7) ∨ (p6 → False)) → ((p2 → p3) ∧ (False ∧ p5))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_22 : (p4 → p4) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    apply False.elim assump_17


variable (p6 p4 : Prop)
theorem file48_82303 : ((((((False → False) → False) ∧ ((p4 ∨ p6) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → False) → False) ∧ ((p4 ∨ p6) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_24 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_24
      apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p7 p1 p3 p6 p4 : Prop)
theorem file48_82869 : (((((True → False) → (p3 → False)) → False) → (((p6 → p1) ∧ (p7 ∧ True)) ∧ ((p2 → True) → (p7 → p3)))) ∨ ((((p1 → False) ∨ (True → False)) ∧ ((p3 → False) ∨ (p7 → False))) ∧ (((p6 ∨ False) → False) → ((p2 → p3) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_59 : ((True → False) → (p3 → False)) := by
    intro assump_8
    intro assump_9
    have assump_60 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_60
    apply False.elim assump_14
  let assump_7 := assump_1 assump_59
  apply False.elim assump_7
  apply And.intro
  have assump_61 : ((True → False) → (p3 → False)) := by
    intro assump_24
    intro assump_25
    have assump_62 : True := by
      apply True.intro
    let assump_30 := assump_24 assump_62
    apply False.elim assump_30
  let assump_23 := assump_1 assump_61
  apply False.elim assump_23
  apply True.intro
  intro assump_37
  intro assump_38
  have assump_63 : ((True → False) → (p3 → False)) := by
    intro assump_46
    intro assump_47
    have assump_64 : True := by
      apply True.intro
    let assump_52 := assump_46 assump_64
    apply False.elim assump_52
  let assump_45 := assump_1 assump_63
  apply False.elim assump_45


variable (p1 p5 p6 p3 : Prop)
theorem file48_84185 : (((((p1 ∧ p5) ∧ (True → False)) → ((p3 → False) ∧ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_43 : (((p1 ∧ p5) ∧ (True → False)) → ((p3 → False) ∧ (p6 → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_44 : True := by
          apply True.intro
        let assump_19 := assump_10 assump_44
        apply False.elim assump_19
    intro assump_23
    cases assump_5
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        have assump_45 : True := by
          apply True.intro
        let assump_36 := assump_27 assump_45
        apply False.elim assump_36
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p2 p3 p1 p0 p5 : Prop)
theorem file48_85101 : (((((p3 ∧ p2) ∨ (False ∨ p1)) → False) ∧ (((True ∨ p3) → False) ∧ ((p0 ∧ p3) → (True → p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_6 assump_17
      apply False.elim assump_13


variable (p4 p2 p6 p7 p3 p1 : Prop)
theorem file48_85555 : ((((((p7 → False) ∧ (p2 ∧ False)) → ((p3 → False) ∨ (p1 ∧ True))) ∨ (((p4 → p6) ∧ (p3 ∨ p1)) → False)) → False) → False) := by
  intro assump_7
  have assump_25 : ((((p7 → False) ∧ (p2 ∧ False)) → ((p3 → False) ∨ (p1 ∧ True))) ∨ (((p4 → p6) ∧ (p3 ∨ p1)) → False)) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
  let assump_10 := assump_7 assump_25
  apply False.elim assump_10


variable (p1 p4 p7 p0 p5 : Prop)
theorem file48_86141 : ((((((p1 ∨ True) → False) → ((p7 ∨ p1) ∧ (p0 → p4))) ∨ (((p5 → False) ∨ (p0 ∨ True)) → ((p4 → False) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p1 ∨ True) → False) → ((p7 ∨ p1) ∧ (p0 → p4))) ∨ (((p5 → False) ∨ (p0 ∨ True)) → ((p4 → False) ∧ (False → False)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_25 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_25
    apply False.elim assump_8
    intro assump_12
    have assump_26 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_17 := assump_5 assump_26
    apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p6 p4 p0 p1 : Prop)
theorem file48_86949 : ((((((p6 ∨ True) ∧ (False → False)) ∨ ((p0 ∨ False) → (True ∧ p4))) ∨ (((p4 ∧ p1) → False) ∧ ((p0 ∨ p1) ∨ (p0 → p3)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 ∨ True) ∧ (False → False)) ∨ ((p0 ∨ False) → (True ∧ p4))) ∨ (((p4 ∧ p1) → False) ∧ ((p0 ∨ p1) ∨ (p0 → p3)))) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p3 p1 p4 p2 p5 p6 : Prop)
theorem file48_87520 : (((((p5 → False) → (p6 → p3)) → False) → (((p7 ∧ False) ∧ (p7 → False)) → False)) ∨ ((((p2 → False) → (p7 → p4)) → ((True ∧ p3) → (p3 → False))) ∧ (((p1 → False) → (p2 → False)) ∧ ((p7 ∧ p5) → False)))) := by
  apply Or.inl
  intro assump_15
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      apply False.elim assump_20


variable (p7 p5 p1 p4 p6 : Prop)
theorem file48_87982 : ((((((p4 → False) → (p1 → p7)) → False) → False) ∧ ((((False → p7) → (p7 ∨ False)) ∧ ((p5 ∧ True) ∨ (p6 → False))) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_48 : ((True → False) → False) := by
              intro assump_23
              have assump_49 : True := by
                apply True.intro
              let assump_26 := assump_23 assump_49
              apply False.elim assump_26
            let assump_22 := assump_7 assump_48
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_50 : ((True → False) → False) := by
            intro assump_38
            have assump_51 : True := by
              apply True.intro
            let assump_41 := assump_38 assump_51
            apply False.elim assump_41
          let assump_37 := assump_7 assump_50
          apply False.elim assump_37


variable (p0 p6 p1 p4 p5 p7 p3 : Prop)
theorem file48_89221 : (((((False → p0) ∧ (True ∨ p6)) ∧ ((True → False) → False)) ∨ (((p5 → False) → False) → ((p7 ∧ p1) → False))) ∨ ((((True ∨ p6) → False) ∧ ((p1 → False) ∨ (p4 → False))) → (((p6 → p1) → (p3 → False)) → ((p0 ∨ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply And.intro
  intro assump_1
  apply False.elim assump_1
  apply Or.inl
  apply True.intro
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p4 p3 p0 p1 p7 p5 : Prop)
theorem file48_89789 : (((((p5 ∨ p1) ∨ (p4 → True)) → ((p4 ∨ p0) → (p1 → True))) ∧ (((p4 ∨ p0) → False) → ((True → False) → False))) ∨ ((((p3 → p7) → (p3 ∨ False)) → False) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro
  intro assump_4
  intro assump_5
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_5 assump_15
  apply False.elim assump_11


variable (p1 p2 p7 p0 p4 : Prop)
theorem file48_90267 : ((((((p2 → False) → (True → p2)) → False) ∨ (((p7 → p4) ∧ (False → True)) → ((p7 ∨ p0) ∨ (p4 ∧ p1)))) ∧ ((((p7 → p7) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_42 : (((p7 → p7) → False) → False) := by
        intro assump_11
        have assump_43 : (p7 → p7) := by
          intro assump_15
          exact assump_15
        let assump_14 := assump_11 assump_43
        apply False.elim assump_14
      let assump_10 := assump_3 assump_42
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_44 : (((p7 → p7) → False) → False) := by
        intro assump_29
        have assump_45 : (p7 → p7) := by
          intro assump_33
          exact assump_33
        let assump_32 := assump_29 assump_45
        apply False.elim assump_32
      let assump_28 := assump_3 assump_44
      apply False.elim assump_28


variable (p6 p1 p2 p7 p3 : Prop)
theorem file48_91283 : (((((p7 → p6) ∧ (p1 → False)) → False) ∧ (((p3 → False) ∧ (p2 → False)) ∧ ((True → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_21 : (True → True) := by
          intro assump_17
          apply True.intro
        let assump_16 := assump_7 assump_21
        apply False.elim assump_16


variable (p3 p7 p0 p1 p4 p6 : Prop)
theorem file48_91817 : (((((p7 → False) ∨ (p3 ∧ p1)) ∧ ((p4 ∧ p1) ∧ (p7 → p6))) ∧ (((p7 ∨ p0) → (p3 ∨ True)) ∧ ((p1 → False) ∧ (False → p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                have assump_66 : p1 := by
                  exact assump_13
                let assump_31 := assump_24 assump_66
                apply False.elim assump_31
      case inr assump_7 =>
        cases assump_7
        case intro assump_35 assump_36 =>
          cases assump_5
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              cases assump_3
              case intro assump_51 assump_52 =>
                cases assump_52
                case intro assump_55 assump_56 =>
                  have assump_67 : p1 := by
                    exact assump_44
                  let assump_62 := assump_55 assump_67
                  apply False.elim assump_62


variable (p4 : Prop)
theorem file48_93200 : ((((((False → False) ∨ (p4 → False)) → False) → False) → False) → False) := by
  intro assump_7
  have assump_24 : ((((False → False) ∨ (p4 → False)) → False) → False) := by
    intro assump_11
    have assump_25 : ((False → False) ∨ (p4 → False)) := by
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_11 assump_25
    apply False.elim assump_14
  let assump_10 := assump_7 assump_24
  apply False.elim assump_10


variable (p1 p6 p3 p2 p5 p4 : Prop)
theorem file48_93727 : ((((((False → False) → (p6 ∧ p6)) ∧ ((True ∧ False) ∧ (p4 ∨ p1))) → False) → ((((p5 → False) ∧ (p5 ∧ p5)) ∨ ((p3 ∧ True) ∧ (p1 ∧ False))) ∧ (((p1 → False) → (True → p3)) ∧ ((p2 → p2) ∨ (p2 → p6))))) → False) := by
  intro assump_1
  have assump_52 : ((((False → False) → (p6 ∧ p6)) ∧ ((True ∧ False) ∧ (p4 ∨ p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_52
  let assump_18 := And.left assump_4
  cases assump_18
  case inl assump_20 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        have assump_53 : p5 := by
          exact assump_27
        let assump_34 := assump_22 assump_53
        apply False.elim assump_34
  case inr assump_21 =>
    cases assump_21
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_39
        case intro assump_46 assump_47 =>
          apply False.elim assump_47


variable (p1 p2 p4 p3 p7 p0 : Prop)
theorem file48_94977 : (((((p0 ∨ p4) ∧ (p3 → p3)) → ((True → p2) → (p7 → False))) → (((False ∧ p2) → (p0 → True)) ∨ ((False ∧ p4) → False))) ∨ ((((False → p1) ∧ (p3 → False)) → ((p7 ∨ p4) ∨ (p3 → False))) ∧ (((False ∧ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p7 p2 p1 p4 p0 p3 p5 : Prop)
theorem file48_95365 : ((((((p7 ∨ True) → (p3 ∨ p1)) ∧ ((p4 ∧ p3) → (p3 → p2))) → (((p5 ∧ p1) ∧ (p5 ∧ p7)) → ((p0 ∨ p2) → False))) ∧ ((((False → p1) → False) ∨ ((False → False) → False)) ∧ (((p0 ∧ True) ∨ (p0 ∨ p1)) ∨ ((p1 → False) ∨ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              have assump_138 : (False → p1) := by
                intro assump_24
                apply False.elim assump_24
              let assump_23 := assump_8 assump_138
              apply False.elim assump_23
          case inr assump_15 =>
            cases assump_15
            case inl assump_30 =>
              have assump_139 : (False → p1) := by
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_8 assump_139
              apply False.elim assump_35
            case inr assump_31 =>
              have assump_140 : (False → p1) := by
                intro assump_46
                apply False.elim assump_46
              let assump_45 := assump_8 assump_140
              apply False.elim assump_45
        case inr assump_13 =>
          cases assump_13
          case inl assump_52 =>
            have assump_141 : (False → p1) := by
              intro assump_58
              apply False.elim assump_58
            let assump_57 := assump_8 assump_141
            apply False.elim assump_57
          case inr assump_53 =>
            have assump_142 : (False → p1) := by
              intro assump_68
              apply False.elim assump_68
            let assump_67 := assump_8 assump_142
            apply False.elim assump_67
      case inr assump_9 =>
        cases assump_7
        case inl assump_76 =>
          cases assump_76
          case inl assump_78 =>
            cases assump_78
            case intro assump_80 assump_81 =>
              have assump_143 : (False → False) := by
                intro assump_88
                apply False.elim assump_88
              let assump_87 := assump_9 assump_143
              apply False.elim assump_87
          case inr assump_79 =>
            cases assump_79
            case inl assump_94 =>
              have assump_144 : (False → False) := by
                intro assump_100
                apply False.elim assump_100
              let assump_99 := assump_9 assump_144
              apply False.elim assump_99
            case inr assump_95 =>
              have assump_145 : (False → False) := by
                intro assump_110
                apply False.elim assump_110
              let assump_109 := assump_9 assump_145
              apply False.elim assump_109
        case inr assump_77 =>
          cases assump_77
          case inl assump_116 =>
            have assump_146 : (False → False) := by
              intro assump_122
              apply False.elim assump_122
            let assump_121 := assump_9 assump_146
            apply False.elim assump_121
          case inr assump_117 =>
            have assump_147 : (False → False) := by
              intro assump_132
              apply False.elim assump_132
            let assump_131 := assump_9 assump_147
            apply False.elim assump_131


variable (p1 p3 p2 p5 p4 p0 p6 p7 : Prop)
theorem file48_98909 : (((((p6 → p0) ∨ (p7 ∧ False)) → ((p3 ∧ p7) → (p6 → True))) ∨ (((p5 → False) ∧ (p2 → p1)) → False)) ∨ ((((p0 → p1) → (False → False)) ∧ ((p0 ∧ p3) → (p4 → True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p6 p5 p1 p3 p0 p7 p2 p4 : Prop)
theorem file48_99253 : ((((((p5 ∧ p0) ∨ (p4 ∧ p1)) → ((p7 ∨ p4) ∨ (True → p0))) ∨ (((p2 ∨ p3) ∧ (p6 ∨ p7)) → ((p7 ∨ p7) ∧ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p5 ∧ p0) ∨ (p4 ∧ p1)) → ((p7 ∨ p4) ∨ (True → p0))) ∨ (((p2 ∨ p3) ∧ (p6 ∨ p7)) → ((p7 ∨ p7) ∧ (p3 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        intro assump_14
        exact assump_9
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        apply Or.inl
        apply Or.inr
        exact assump_17
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p2 p6 p0 p3 p1 p4 p7 p5 : Prop)
theorem file48_100037 : ((((((False ∧ True) ∧ (p3 ∨ p7)) → ((p0 ∧ p2) ∧ (False ∧ p0))) ∧ (((False ∨ p7) → (p5 → False)) ∨ ((p3 → p5) ∨ (False ∨ False)))) ∧ ((((p0 → False) → (True ∨ p7)) ∨ ((p4 ∨ p0) → (p1 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_40 : (((p0 → False) → (True ∨ p7)) ∨ ((p4 ∨ p0) → (p1 ∨ p6))) := by
          apply Or.inl
          intro assump_15
          apply Or.inl
          apply True.intro
        let assump_14 := assump_3 assump_40
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_21 =>
          have assump_41 : (((p0 → False) → (True ∨ p7)) ∨ ((p4 ∨ p0) → (p1 ∨ p6))) := by
            apply Or.inl
            intro assump_28
            apply Or.inl
            apply True.intro
          let assump_27 := assump_3 assump_41
          apply False.elim assump_27
        case inr assump_22 =>
          cases assump_22
          case inl assump_34 =>
            apply False.elim assump_34
          case inr assump_35 =>
            apply False.elim assump_35


variable (p4 p1 p3 p5 p0 p6 p7 : Prop)
theorem file48_101310 : (((((p6 ∧ False) → False) ∨ ((p1 ∧ False) → False)) ∨ (((p7 ∨ p7) ∨ (False → False)) ∧ ((p4 ∧ False) → False))) ∧ ((((p3 → p1) → (p0 ∨ p3)) ∧ ((True ∧ p4) ∧ (p0 → False))) → (((p3 → p7) ∨ (p7 ∧ p7)) → ((p5 → True) ∧ (False → True))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  intro assump_8
  intro assump_9
  apply And.intro
  intro assump_10
  apply True.intro
  intro assump_11
  apply True.intro


variable (p7 p6 p0 : Prop)
theorem file48_101874 : ((((((p6 → p6) ∨ (p0 → False)) → False) → False) → ((((True → False) → (False → False)) → False) ∨ (((p7 → False) → False) ∧ ((True → False) ∨ (p7 ∧ False))))) → False) := by
  intro assump_1
  have assump_46 : ((((p6 → p6) ∨ (p0 → False)) → False) → False) := by
    intro assump_5
    have assump_47 : ((p6 → p6) ∨ (p0 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_47
    apply False.elim assump_8
  let assump_4 := assump_1 assump_46
  cases assump_4
  case inl assump_16 =>
    have assump_48 : ((True → False) → (False → False)) := by
      intro assump_21
      intro assump_22
      apply False.elim assump_22
    let assump_20 := assump_16 assump_48
    apply False.elim assump_20
  case inr assump_17 =>
    cases assump_17
    case intro assump_28 assump_29 =>
      cases assump_29
      case inl assump_32 =>
        have assump_49 : True := by
          apply True.intro
        let assump_36 := assump_32 assump_49
        apply False.elim assump_36
      case inr assump_33 =>
        cases assump_33
        case intro assump_40 assump_41 =>
          apply False.elim assump_41


variable (p0 p7 p3 p6 : Prop)
theorem file48_103090 : (((((p6 → True) ∨ (p3 → False)) ∨ ((p6 ∧ p7) ∧ (p0 ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p6 → True) ∨ (p3 → False)) ∨ ((p6 ∧ p7) ∧ (p0 ∨ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p4 p5 : Prop)
theorem file48_103460 : (((((False ∨ p2) → (True ∨ True)) ∨ ((p5 ∧ p2) ∨ (p4 → False))) → False) → False) := by
  intro assump_11
  have assump_25 : (((False ∨ p2) → (True ∨ True)) ∨ ((p5 ∧ p2) ∨ (p4 → False))) := by
    apply Or.inl
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply False.elim assump_16
    case inr assump_17 =>
      apply Or.inl
      apply True.intro
  let assump_14 := assump_11 assump_25
  apply False.elim assump_14


variable (p5 p0 p1 p3 : Prop)
theorem file48_103959 : ((((((p1 ∧ p1) ∧ (p5 → p3)) ∧ ((p0 → p0) → False)) → (((p1 → p5) ∨ (p0 → p0)) ∨ ((False ∨ p0) ∨ (p0 → False)))) → False) → False) := by
  intro assump_5
  have assump_38 : ((((p1 ∧ p1) ∧ (p5 → p3)) ∧ ((p0 → p0) → False)) → (((p1 → p5) ∨ (p0 → p0)) ∨ ((False ∨ p0) ∨ (p0 → False)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply Or.inl
          intro assump_24
          have assump_39 : (p0 → p0) := by
            intro assump_29
            exact assump_29
          let assump_28 := assump_11 assump_39
          apply False.elim assump_28
  let assump_8 := assump_5 assump_38
  apply False.elim assump_8


variable (p6 p3 p7 p4 p0 p2 : Prop)
theorem file48_104831 : (((((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) → False) → ((((p7 → False) ∧ (True ∨ p4)) ∧ ((p7 → False) ∧ (p4 ∨ p3))) ∧ (((p0 ∨ p4) ∧ (p4 ∨ False)) → ((p3 ∨ p2) → False)))) := by
  intro assump_31
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_32
  have assump_151 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_38
    apply False.elim assump_38
  let assump_37 := assump_31 assump_151
  apply False.elim assump_37
  apply Or.inl
  apply True.intro
  apply And.intro
  intro assump_46
  have assump_152 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_52
    apply False.elim assump_52
  let assump_51 := assump_31 assump_152
  apply False.elim assump_51
  have assump_153 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
    apply Or.inl
    apply Or.inl
    intro assump_61
    apply False.elim assump_61
  let assump_60 := assump_31 assump_153
  apply False.elim assump_60
  intro assump_67
  intro assump_68
  cases assump_68
  case inl assump_69 =>
    cases assump_67
    case intro assump_73 assump_74 =>
      cases assump_73
      case inl assump_75 =>
        cases assump_74
        case inl assump_79 =>
          have assump_154 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
            apply Or.inl
            apply Or.inl
            intro assump_86
            apply False.elim assump_86
          let assump_85 := assump_31 assump_154
          apply False.elim assump_85
        case inr assump_80 =>
          apply False.elim assump_80
      case inr assump_76 =>
        cases assump_74
        case inl assump_96 =>
          have assump_155 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
            apply Or.inl
            apply Or.inl
            intro assump_103
            apply False.elim assump_103
          let assump_102 := assump_31 assump_155
          apply False.elim assump_102
        case inr assump_97 =>
          apply False.elim assump_97
  case inr assump_70 =>
    cases assump_67
    case intro assump_113 assump_114 =>
      cases assump_113
      case inl assump_115 =>
        cases assump_114
        case inl assump_119 =>
          have assump_156 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
            apply Or.inl
            apply Or.inl
            intro assump_126
            apply False.elim assump_126
          let assump_125 := assump_31 assump_156
          apply False.elim assump_125
        case inr assump_120 =>
          apply False.elim assump_120
      case inr assump_116 =>
        cases assump_114
        case inl assump_136 =>
          have assump_157 : (((False → p6) ∨ (p6 ∨ p0)) ∨ ((p4 ∨ p3) ∧ (True ∨ p0))) := by
            apply Or.inl
            apply Or.inl
            intro assump_143
            apply False.elim assump_143
          let assump_142 := assump_31 assump_157
          apply False.elim assump_142
        case inr assump_137 =>
          apply False.elim assump_137


variable (p0 p4 p7 p5 p1 p6 p3 : Prop)
theorem file48_108012 : (((((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) → False) → ((((p0 → p4) ∨ (p3 → False)) ∧ ((p6 ∨ p4) ∧ (p3 → p6))) → (((p6 ∨ p7) ∧ (p3 ∨ p5)) ∧ ((False ∨ p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          apply Or.inl
          exact assump_11
        case inr assump_12 =>
          have assump_180 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_26
            apply True.intro
          let assump_25 := assump_1 assump_180
          apply False.elim assump_25
    case inr assump_6 =>
      cases assump_4
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          apply Or.inl
          exact assump_34
        case inr assump_35 =>
          have assump_181 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_49
            apply True.intro
          let assump_48 := assump_1 assump_181
          apply False.elim assump_48
  cases assump_2
  case intro assump_53 assump_54 =>
    cases assump_53
    case inl assump_55 =>
      cases assump_54
      case intro assump_59 assump_60 =>
        cases assump_59
        case inl assump_61 =>
          have assump_182 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_70
            apply True.intro
          let assump_69 := assump_1 assump_182
          apply False.elim assump_69
        case inr assump_62 =>
          have assump_183 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_81
            apply True.intro
          let assump_80 := assump_1 assump_183
          apply False.elim assump_80
    case inr assump_56 =>
      cases assump_54
      case intro assump_87 assump_88 =>
        cases assump_87
        case inl assump_89 =>
          have assump_184 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_98
            apply True.intro
          let assump_97 := assump_1 assump_184
          apply False.elim assump_97
        case inr assump_90 =>
          have assump_185 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
            apply Or.inl
            apply Or.inl
            intro assump_109
            apply True.intro
          let assump_108 := assump_1 assump_185
          apply False.elim assump_108
  intro assump_113
  cases assump_113
  case inl assump_114 =>
    apply False.elim assump_114
  case inr assump_115 =>
    cases assump_2
    case intro assump_120 assump_121 =>
      cases assump_120
      case inl assump_122 =>
        cases assump_121
        case intro assump_126 assump_127 =>
          cases assump_126
          case inl assump_128 =>
            have assump_186 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
              apply Or.inl
              apply Or.inl
              intro assump_137
              apply True.intro
            let assump_136 := assump_1 assump_186
            apply False.elim assump_136
          case inr assump_129 =>
            have assump_187 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
              apply Or.inl
              apply Or.inl
              intro assump_148
              apply True.intro
            let assump_147 := assump_1 assump_187
            apply False.elim assump_147
      case inr assump_123 =>
        cases assump_121
        case intro assump_154 assump_155 =>
          cases assump_154
          case inl assump_156 =>
            have assump_188 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
              apply Or.inl
              apply Or.inl
              intro assump_165
              apply True.intro
            let assump_164 := assump_1 assump_188
            apply False.elim assump_164
          case inr assump_157 =>
            have assump_189 : (((p6 → True) ∨ (p7 ∧ p7)) ∨ ((p1 → True) ∨ (True ∨ p5))) := by
              apply Or.inl
              apply Or.inl
              intro assump_176
              apply True.intro
            let assump_175 := assump_1 assump_189
            apply False.elim assump_175


variable (p3 p6 p4 : Prop)
theorem file48_112729 : (((((p3 ∨ True) ∧ (p4 → p4)) ∨ ((p6 ∨ p3) → False)) → False) → False) := by
  intro assump_9
  have assump_19 : (((p3 ∨ True) ∧ (p4 → p4)) ∨ ((p6 ∨ p3) → False)) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply True.intro
    intro assump_13
    exact assump_13
  let assump_12 := assump_9 assump_19
  apply False.elim assump_12


variable (p6 p3 p1 p0 : Prop)
theorem file48_113133 : ((((((True → False) → (p3 ∨ p3)) → False) → (((p0 → p1) → False) → ((p1 → p0) → (p0 → p6)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((True → False) → (p3 ∨ p3)) → False) → (((p0 → p1) → False) → ((p1 → p0) → (p0 → p6)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    have assump_32 : ((True → False) → (p3 ∨ p3)) := by
      intro assump_18
      have assump_33 : True := by
        apply True.intro
      let assump_21 := assump_18 assump_33
      apply False.elim assump_21
    let assump_17 := assump_5 assump_32
    apply False.elim assump_17
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p6 p4 p5 p7 p2 : Prop)
theorem file48_113868 : (((((p1 ∧ True) ∧ (True → False)) → ((p1 ∨ p7) → (p7 → p6))) ∨ (((p4 ∨ p7) → False) → False)) ∨ ((((p2 → False) ∨ (p7 → False)) → ((p6 ∨ p5) ∧ (p6 ∨ p6))) ∧ (((p1 ∨ True) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_40 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_40
        apply False.elim assump_20
  case inr assump_7 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        have assump_41 : True := by
          apply True.intro
        let assump_36 := assump_27 assump_41
        apply False.elim assump_36


variable (p4 p3 p5 p2 p6 p0 p1 : Prop)
theorem file48_114796 : (((((True ∧ p2) ∧ (p5 ∧ False)) ∧ ((p3 ∨ p1) ∨ (p6 → False))) ∧ (((p6 ∨ p6) ∨ (p6 → p3)) → False)) → ((((False ∧ p2) → (p0 ∧ p3)) ∨ ((p4 ∧ p0) ∨ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            cases assump_12
            case intro assump_19 assump_20 =>
              apply False.elim assump_20
  case inr assump_4 =>
    cases assump_4
    case inl assump_25 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_1
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              cases assump_37
              case intro assump_39 assump_40 =>
                cases assump_38
                case intro assump_45 assump_46 =>
                  apply False.elim assump_46
    case inr assump_26 =>
      cases assump_1
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_55
          case intro assump_57 assump_58 =>
            cases assump_57
            case intro assump_59 assump_60 =>
              cases assump_58
              case intro assump_65 assump_66 =>
                apply False.elim assump_66


variable (p3 p0 p6 p4 p7 p5 p1 p2 : Prop)
theorem file48_116441 : (((((p6 ∧ p6) → (p4 ∨ p5)) ∧ ((p2 ∨ True) → False)) → (((p5 → p7) ∨ (p1 → p3)) → ((p5 ∨ p3) → (False ∨ p1)))) ∨ ((((p0 → False) ∨ (p6 ∧ p6)) ∨ ((True ∧ p2) ∧ (p2 → p4))) ∨ (((p2 ∧ p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        have assump_62 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_13 assump_62
        apply False.elim assump_18
    case inr assump_9 =>
      cases assump_1
      case intro assump_24 assump_25 =>
        have assump_63 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_30 := assump_25 assump_63
        apply False.elim assump_30
  case inr assump_5 =>
    cases assump_2
    case inl assump_36 =>
      cases assump_1
      case intro assump_40 assump_41 =>
        have assump_64 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_46 := assump_41 assump_64
        apply False.elim assump_46
    case inr assump_37 =>
      cases assump_1
      case intro assump_52 assump_53 =>
        have assump_65 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_58 := assump_53 assump_65
        apply False.elim assump_58


variable (p6 p2 p1 : Prop)
theorem file48_117907 : ((((((False → False) → False) → False) → (((p2 ∧ False) ∧ (p6 ∨ p1)) → ((p6 ∨ p1) → False))) → False) → False) := by
  intro assump_8
  have assump_40 : ((((False → False) → False) → False) → (((p2 ∧ False) ∧ (p6 ∨ p1)) → ((p6 ∨ p1) → False))) := by
    intro assump_12
    intro assump_13
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      cases assump_13
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
    case inr assump_16 =>
      cases assump_13
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          apply False.elim assump_32
  let assump_11 := assump_8 assump_40
  apply False.elim assump_11


variable (p3 p6 p5 p1 : Prop)
theorem file48_118740 : (((((False ∨ True) → False) → ((p3 ∨ p5) → (p1 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_46 : (((False ∨ True) → False) → ((p3 ∨ p5) → (p1 ∧ p6))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      have assump_47 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_5 assump_47
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_48 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_21 := assump_5 assump_48
      apply False.elim assump_21
    cases assump_6
    case inl assump_25 =>
      have assump_49 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_31 := assump_5 assump_49
      apply False.elim assump_31
    case inr assump_26 =>
      have assump_50 : (False ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_39 := assump_5 assump_50
      apply False.elim assump_39
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p1 p5 p6 p0 p4 p7 p3 : Prop)
theorem file48_119900 : (((((p7 ∧ p3) ∧ (p3 → False)) → False) ∧ (((p7 ∧ False) ∧ (True → False)) ∧ ((p6 ∧ p0) ∨ (p7 → False)))) ∨ ((((True → False) ∧ (p3 ∧ p1)) → ((p5 → True) ∧ (p6 → False))) ∧ (((p5 ∨ p5) ∧ (False ∧ p4)) → ((p0 ∧ p6) → (p1 ∧ p0))))) := by
  apply Or.inr
  apply And.intro
  intro assump_20
  apply And.intro
  intro assump_21
  apply True.intro
  intro assump_22
  cases assump_20
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      have assump_87 : True := by
        apply True.intro
      let assump_37 := assump_25 assump_87
      apply False.elim assump_37
  intro assump_41
  intro assump_42
  apply And.intro
  cases assump_42
  case intro assump_43 assump_44 =>
    cases assump_41
    case intro assump_49 assump_50 =>
      cases assump_49
      case inl assump_51 =>
        cases assump_50
        case intro assump_55 assump_56 =>
          apply False.elim assump_55
      case inr assump_52 =>
        cases assump_50
        case intro assump_61 assump_62 =>
          apply False.elim assump_61
  cases assump_42
  case intro assump_65 assump_66 =>
    cases assump_41
    case intro assump_71 assump_72 =>
      cases assump_71
      case inl assump_73 =>
        cases assump_72
        case intro assump_77 assump_78 =>
          apply False.elim assump_77
      case inr assump_74 =>
        cases assump_72
        case intro assump_83 assump_84 =>
          apply False.elim assump_83


variable (p3 p1 p0 p5 p2 p4 p6 p7 : Prop)
theorem file48_121418 : ((((((p0 ∨ p4) ∧ (p7 ∨ p7)) → ((p3 → False) → (p6 → True))) ∨ (((p6 → p2) ∨ (p7 ∧ p2)) → ((p6 → p1) → (p5 ∨ p1)))) → False) → False) := by
  intro assump_5
  have assump_15 : ((((p0 ∨ p4) ∧ (p7 ∨ p7)) → ((p3 → False) → (p6 → True))) ∨ (((p6 → p2) ∨ (p7 ∧ p2)) → ((p6 → p1) → (p5 ∨ p1)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    intro assump_11
    apply True.intro
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p0 p4 p1 p6 p3 p2 : Prop)
theorem file48_121934 : ((((((p2 → p1) → (p2 ∧ p6)) ∧ ((p3 → True) → (p1 ∧ False))) → (((True ∧ p4) → False) ∧ ((p3 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p2 → p1) → (p2 ∧ p6)) ∧ ((p3 → True) → (p1 ∧ False))) → (((True ∧ p4) → False) ∧ ((p3 → p0) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        have assump_46 : (p3 → True) := by
          intro assump_20
          apply True.intro
        let assump_19 := assump_14 assump_46
        let assump_21 := And.right assump_19
        apply False.elim assump_21
    intro assump_26
    cases assump_5
    case intro assump_29 assump_30 =>
      have assump_47 : (p3 → True) := by
        intro assump_36
        apply True.intro
      let assump_35 := assump_30 assump_47
      let assump_37 := And.right assump_35
      apply False.elim assump_37
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p5 p3 p7 p4 p2 p1 : Prop)
theorem file48_123022 : (((((p7 ∨ p1) → False) → ((p5 ∧ p1) → (p2 → p3))) → False) → ((((False ∨ p7) ∧ (p2 → p5)) → ((p2 ∧ p4) → (p3 ∧ p2))) ∨ (((p3 → False) → (False ∧ p7)) ∨ ((p7 ∧ p3) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        apply False.elim assump_14
      case inr assump_15 =>
        have assump_64 : (((p7 ∨ p1) → False) → ((p5 ∧ p1) → (p2 → p3))) := by
          intro assump_28
          intro assump_29
          intro assump_30
          cases assump_29
          case intro assump_33 assump_34 =>
            have assump_65 : (p7 ∨ p1) := by
              apply Or.inl
              exact assump_15
            let assump_41 := assump_28 assump_65
            apply False.elim assump_41
        let assump_27 := assump_1 assump_64
        apply False.elim assump_27
  cases assump_5
  case intro assump_48 assump_49 =>
    cases assump_4
    case intro assump_54 assump_55 =>
      cases assump_54
      case inl assump_56 =>
        apply False.elim assump_56
      case inr assump_57 =>
        exact assump_48


variable (p2 p5 p7 p0 p1 : Prop)
theorem file48_124308 : (((((p0 ∨ True) ∨ (p7 → False)) → ((p2 ∧ p5) → (p1 ∧ p0))) ∧ (((True → p1) → False) ∧ ((p2 → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (p2 → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p0 p7 p1 p2 p4 : Prop)
theorem file48_124778 : (((((p4 ∨ p0) → False) ∧ ((p4 ∧ p7) ∨ (p0 → p1))) ∧ (((p2 ∧ False) → (p1 ∨ p1)) → ((False → False) → (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_54 : ((p2 ∧ False) → (p1 ∨ p1)) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
          let assump_18 := assump_3 assump_54
          have assump_55 : (False → False) := by
            intro assump_27
            apply False.elim assump_27
          let assump_26 := assump_18 assump_55
          have assump_56 : True := by
            apply True.intro
          let assump_30 := assump_26 assump_56
          apply False.elim assump_30
      case inr assump_9 =>
        have assump_57 : ((p2 ∧ False) → (p1 ∨ p1)) := by
          intro assump_39
          cases assump_39
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
        let assump_38 := assump_3 assump_57
        have assump_58 : (False → False) := by
          intro assump_47
          apply False.elim assump_47
        let assump_46 := assump_38 assump_58
        have assump_59 : True := by
          apply True.intro
        let assump_50 := assump_46 assump_59
        apply False.elim assump_50


variable (p0 p6 : Prop)
theorem file48_126321 : (((((False ∧ False) ∧ (p0 ∨ p6)) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ False) ∧ (p0 ∨ p6)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 p1 p7 p2 p3 p0 : Prop)
theorem file48_126764 : (((((p5 ∧ False) ∨ (p5 ∨ p2)) ∧ ((p7 → False) ∧ (p4 → False))) → (((p5 ∧ p1) → (p7 ∧ p5)) ∧ ((p3 → p7) ∧ (p5 ∧ p4)))) → ((((p4 ∧ False) → (False → p0)) → False) → (((False → False) ∨ (p2 → p7)) → ((True → False) → (p3 ∧ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_3
  case inl assump_7 =>
    have assump_73 : ((p4 ∧ False) → (False → p0)) := by
      intro assump_17
      intro assump_18
      apply False.elim assump_18
    let assump_16 := assump_2 assump_73
    apply False.elim assump_16
  case inr assump_8 =>
    have assump_74 : ((p4 ∧ False) → (False → p0)) := by
      intro assump_32
      intro assump_33
      apply False.elim assump_33
    let assump_31 := assump_2 assump_74
    apply False.elim assump_31
  cases assump_3
  case inl assump_41 =>
    have assump_75 : ((p4 ∧ False) → (False → p0)) := by
      intro assump_51
      intro assump_52
      apply False.elim assump_52
    let assump_50 := assump_2 assump_75
    apply False.elim assump_50
  case inr assump_42 =>
    have assump_76 : ((p4 ∧ False) → (False → p0)) := by
      intro assump_66
      intro assump_67
      apply False.elim assump_67
    let assump_65 := assump_2 assump_76
    apply False.elim assump_65


variable (p1 p7 p2 p6 p5 : Prop)
theorem file48_128089 : ((((((p7 ∨ p5) ∨ (True ∨ p2)) → False) → (((p1 ∧ p6) → False) ∧ ((p5 → False) → False))) → ((((True → False) → False) → False) ∧ (((p5 → p7) → (p1 → False)) → False))) → False) := by
  intro assump_1
  have assump_40 : ((((p7 ∨ p5) ∨ (True ∨ p2)) → False) → (((p1 ∧ p6) → False) ∧ ((p5 → False) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_41 : ((p7 ∨ p5) ∨ (True ∨ p2)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_15 := assump_5 assump_41
      apply False.elim assump_15
    intro assump_19
    have assump_42 : ((p7 ∨ p5) ∨ (True ∨ p2)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_24 := assump_5 assump_42
    apply False.elim assump_24
  let assump_4 := assump_1 assump_40
  let assump_28 := And.left assump_4
  have assump_43 : ((True → False) → False) := by
    intro assump_30
    have assump_44 : True := by
      apply True.intro
    let assump_33 := assump_30 assump_44
    apply False.elim assump_33
  let assump_29 := assump_28 assump_43
  apply False.elim assump_29


variable (p7 p6 p5 p2 : Prop)
theorem file48_129309 : (((((p2 ∨ p5) ∧ (p5 → False)) ∧ ((p7 ∧ False) ∧ (p6 ∨ p2))) → False) ∨ ((((True → p7) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      case inr assump_7 =>
        cases assump_3
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_27


variable (p4 p5 p1 p7 p6 : Prop)
theorem file48_130047 : ((((((p4 ∧ p6) → (p7 → p4)) ∧ ((p1 → True) ∨ (True → False))) ∨ (((True → False) ∨ (p5 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∧ p6) → (p7 → p4)) ∧ ((p1 → True) ∨ (True → False))) ∨ (((True → False) ∨ (p5 ∨ False)) → False)) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
    apply Or.inl
    intro assump_15
    apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p0 p1 p7 p3 p5 p6 : Prop)
theorem file48_130663 : (((((p1 → False) → False) ∧ ((p7 → False) ∧ (p3 ∧ p3))) → False) → ((((p6 ∨ p6) → (p5 → p2)) → ((p3 ∨ True) ∨ (p6 → p7))) ∨ (((True → False) ∨ (p5 ∧ p3)) → ((p3 → False) ∨ (p2 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply Or.inr
  apply True.intro


