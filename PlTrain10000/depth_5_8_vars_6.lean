variable (p1 p4 p5 p0 p3 : Prop)
theorem file6_41 : ((((((p4 → p4) → (p5 ∨ True)) → ((p5 ∨ p0) → False)) → (((True → p3) ∨ (p0 ∨ p5)) → ((True → False) → (True ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p4 → p4) → (p5 ∨ True)) → ((p5 ∨ p0) → False)) → (((True → p3) ∨ (p0 ∨ p5)) → ((True → False) → (True ∧ p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    apply True.intro
    cases assump_6
    case inl assump_10 =>
      have assump_57 : True := by
        apply True.intro
      let assump_23 := assump_7 assump_57
      apply False.elim assump_23
    case inr assump_11 =>
      cases assump_11
      case inl assump_27 =>
        have assump_58 : ((p4 → p4) → (p5 ∨ True)) := by
          intro assump_34
          apply Or.inr
          apply True.intro
        let assump_33 := assump_5 assump_58
        have assump_59 : (p5 ∨ p0) := by
          apply Or.inr
          exact assump_27
        let assump_37 := assump_33 assump_59
        apply False.elim assump_37
      case inr assump_28 =>
        have assump_60 : ((p4 → p4) → (p5 ∨ True)) := by
          intro assump_46
          apply Or.inl
          exact assump_28
        let assump_45 := assump_5 assump_60
        have assump_61 : (p5 ∨ p0) := by
          apply Or.inl
          exact assump_28
        let assump_49 := assump_45 assump_61
        apply False.elim assump_49
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p4 p6 p0 p3 p1 p2 p7 p5 : Prop)
theorem file6_1544 : ((((((True → True) → False) ∧ ((False → False) → (p2 ∧ p6))) ∧ (((p4 → p6) ∨ (True → False)) ∨ ((p3 → False) ∨ (p2 ∧ p0)))) ∧ ((((p5 ∧ p4) → (p0 ∨ p7)) → ((p5 ∨ p4) → False)) ∧ (((p5 ∧ p7) ∨ (p1 ∧ False)) ∧ ((True ∨ p4) → (p7 ∧ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    have assump_190 : ((p5 ∧ p4) → (p0 ∨ p7)) := by
                      intro assump_41
                      cases assump_41
                      case intro assump_42 assump_43 =>
                        apply Or.inr
                        exact assump_27
                    let assump_40 := assump_18 assump_190
                    have assump_191 : (p5 ∨ p4) := by
                      apply Or.inl
                      exact assump_26
                    let assump_48 := assump_40 assump_191
                    apply False.elim assump_48
                case inr assump_25 =>
                  cases assump_25
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_53
          case inr assump_15 =>
            cases assump_3
            case intro assump_60 assump_61 =>
              cases assump_61
              case intro assump_64 assump_65 =>
                cases assump_64
                case inl assump_66 =>
                  cases assump_66
                  case intro assump_68 assump_69 =>
                    have assump_192 : ((p5 ∧ p4) → (p0 ∨ p7)) := by
                      intro assump_83
                      cases assump_83
                      case intro assump_84 assump_85 =>
                        apply Or.inr
                        exact assump_69
                    let assump_82 := assump_60 assump_192
                    have assump_193 : (p5 ∨ p4) := by
                      apply Or.inl
                      exact assump_68
                    let assump_90 := assump_82 assump_193
                    apply False.elim assump_90
                case inr assump_67 =>
                  cases assump_67
                  case intro assump_94 assump_95 =>
                    apply False.elim assump_95
        case inr assump_13 =>
          cases assump_13
          case inl assump_100 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_105
              case intro assump_108 assump_109 =>
                cases assump_108
                case inl assump_110 =>
                  cases assump_110
                  case intro assump_112 assump_113 =>
                    have assump_194 : ((p5 ∧ p4) → (p0 ∨ p7)) := by
                      intro assump_127
                      cases assump_127
                      case intro assump_128 assump_129 =>
                        apply Or.inr
                        exact assump_113
                    let assump_126 := assump_104 assump_194
                    have assump_195 : (p5 ∨ p4) := by
                      apply Or.inl
                      exact assump_112
                    let assump_134 := assump_126 assump_195
                    apply False.elim assump_134
                case inr assump_111 =>
                  cases assump_111
                  case intro assump_138 assump_139 =>
                    apply False.elim assump_139
          case inr assump_101 =>
            cases assump_101
            case intro assump_144 assump_145 =>
              cases assump_3
              case intro assump_150 assump_151 =>
                cases assump_151
                case intro assump_154 assump_155 =>
                  cases assump_154
                  case inl assump_156 =>
                    cases assump_156
                    case intro assump_158 assump_159 =>
                      have assump_196 : ((p5 ∧ p4) → (p0 ∨ p7)) := by
                        intro assump_173
                        cases assump_173
                        case intro assump_174 assump_175 =>
                          apply Or.inl
                          exact assump_145
                      let assump_172 := assump_150 assump_196
                      have assump_197 : (p5 ∨ p4) := by
                        apply Or.inl
                        exact assump_158
                      let assump_180 := assump_172 assump_197
                      apply False.elim assump_180
                  case inr assump_157 =>
                    cases assump_157
                    case intro assump_184 assump_185 =>
                      apply False.elim assump_185


variable (p1 p0 p2 p7 p5 p6 p3 p4 : Prop)
theorem file6_6665 : (((((p2 ∨ p7) ∧ (p6 → p4)) ∨ ((p2 → p1) → (True → False))) → (((p3 ∨ p0) → (p6 → p6)) ∨ ((p2 ∧ True) ∨ (p2 ∧ p7)))) ∨ ((((p5 → False) ∧ (False ∧ p7)) ∧ ((True ∧ True) → (p1 ∨ True))) → (((p1 ∨ False) ∨ (p1 → p5)) → False))) := by
  apply Or.inl
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        apply Or.inl
        intro assump_22
        intro assump_23
        cases assump_22
        case inl assump_26 =>
          exact assump_23
        case inr assump_27 =>
          exact assump_23
      case inr assump_17 =>
        apply Or.inl
        intro assump_36
        intro assump_37
        cases assump_36
        case inl assump_40 =>
          exact assump_37
        case inr assump_41 =>
          exact assump_37
  case inr assump_13 =>
    apply Or.inl
    intro assump_48
    intro assump_49
    cases assump_48
    case inl assump_52 =>
      exact assump_49
    case inr assump_53 =>
      exact assump_49


variable (p4 p0 p3 p7 p5 : Prop)
theorem file6_7770 : ((((((p0 → p3) → False) ∧ ((False → False) → False)) ∨ (((p4 → p3) → False) → ((p3 ∧ p5) → False))) ∧ ((((p7 → p7) ∨ (p7 → False)) → False) ∧ (((p0 ∧ True) ∧ (p4 ∧ p4)) ∨ ((False → False) ∨ (p0 ∨ False))))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_26
        case intro assump_35 assump_36 =>
          cases assump_36
          case inl assump_39 =>
            cases assump_39
            case intro assump_41 assump_42 =>
              cases assump_41
              case intro assump_43 assump_44 =>
                cases assump_42
                case intro assump_49 assump_50 =>
                  have assump_149 : ((p7 → p7) ∨ (p7 → False)) := by
                    apply Or.inl
                    intro assump_59
                    exact assump_59
                  let assump_58 := assump_35 assump_149
                  apply False.elim assump_58
          case inr assump_40 =>
            cases assump_40
            case inl assump_65 =>
              have assump_150 : ((p7 → p7) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_71
                exact assump_71
              let assump_70 := assump_35 assump_150
              apply False.elim assump_70
            case inr assump_66 =>
              cases assump_66
              case inl assump_77 =>
                have assump_151 : ((p7 → p7) ∨ (p7 → False)) := by
                  apply Or.inl
                  intro assump_83
                  exact assump_83
                let assump_82 := assump_35 assump_151
                apply False.elim assump_82
              case inr assump_78 =>
                apply False.elim assump_78
    case inr assump_28 =>
      cases assump_26
      case intro assump_93 assump_94 =>
        cases assump_94
        case inl assump_97 =>
          cases assump_97
          case intro assump_99 assump_100 =>
            cases assump_99
            case intro assump_101 assump_102 =>
              cases assump_100
              case intro assump_107 assump_108 =>
                have assump_152 : ((p7 → p7) ∨ (p7 → False)) := by
                  apply Or.inl
                  intro assump_117
                  exact assump_117
                let assump_116 := assump_93 assump_152
                apply False.elim assump_116
        case inr assump_98 =>
          cases assump_98
          case inl assump_123 =>
            have assump_153 : ((p7 → p7) ∨ (p7 → False)) := by
              apply Or.inl
              intro assump_129
              exact assump_129
            let assump_128 := assump_93 assump_153
            apply False.elim assump_128
          case inr assump_124 =>
            cases assump_124
            case inl assump_135 =>
              have assump_154 : ((p7 → p7) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_141
                exact assump_141
              let assump_140 := assump_93 assump_154
              apply False.elim assump_140
            case inr assump_136 =>
              apply False.elim assump_136


variable (p5 p2 p4 p1 p7 p0 : Prop)
theorem file6_11050 : ((((((p1 → False) → False) ∧ ((False → False) ∨ (p7 ∨ True))) ∧ (((p7 ∧ False) → False) → False)) ∧ ((((p2 → p5) ∨ (p0 → False)) ∧ ((p1 → False) ∧ (p5 ∨ p1))) ∨ (((p4 ∨ p2) → False) ∧ ((p0 ∨ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_3
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    have assump_287 : ((p7 ∧ False) → False) := by
                      intro assump_36
                      cases assump_36
                      case intro assump_37 assump_38 =>
                        apply False.elim assump_38
                    let assump_35 := assump_5 assump_287
                    apply False.elim assump_35
                  case inr assump_29 =>
                    have assump_288 : p1 := by
                      exact assump_29
                    let assump_49 := assump_24 assump_288
                    apply False.elim assump_49
              case inr assump_21 =>
                cases assump_19
                case intro assump_55 assump_56 =>
                  cases assump_56
                  case inl assump_59 =>
                    have assump_289 : ((p7 ∧ False) → False) := by
                      intro assump_67
                      cases assump_67
                      case intro assump_68 assump_69 =>
                        apply False.elim assump_69
                    let assump_66 := assump_5 assump_289
                    apply False.elim assump_66
                  case inr assump_60 =>
                    have assump_290 : p1 := by
                      exact assump_60
                    let assump_80 := assump_55 assump_290
                    apply False.elim assump_80
          case inr assump_17 =>
            cases assump_17
            case intro assump_84 assump_85 =>
              have assump_291 : ((p7 ∧ False) → False) := by
                intro assump_93
                cases assump_93
                case intro assump_94 assump_95 =>
                  apply False.elim assump_95
              let assump_92 := assump_5 assump_291
              apply False.elim assump_92
        case inr assump_11 =>
          cases assump_11
          case inl assump_103 =>
            cases assump_3
            case inl assump_109 =>
              cases assump_109
              case intro assump_111 assump_112 =>
                cases assump_111
                case inl assump_113 =>
                  cases assump_112
                  case intro assump_117 assump_118 =>
                    cases assump_118
                    case inl assump_121 =>
                      have assump_292 : ((p7 ∧ False) → False) := by
                        intro assump_129
                        cases assump_129
                        case intro assump_130 assump_131 =>
                          apply False.elim assump_131
                      let assump_128 := assump_5 assump_292
                      apply False.elim assump_128
                    case inr assump_122 =>
                      have assump_293 : p1 := by
                        exact assump_122
                      let assump_142 := assump_117 assump_293
                      apply False.elim assump_142
                case inr assump_114 =>
                  cases assump_112
                  case intro assump_148 assump_149 =>
                    cases assump_149
                    case inl assump_152 =>
                      have assump_294 : ((p7 ∧ False) → False) := by
                        intro assump_160
                        cases assump_160
                        case intro assump_161 assump_162 =>
                          apply False.elim assump_162
                      let assump_159 := assump_5 assump_294
                      apply False.elim assump_159
                    case inr assump_153 =>
                      have assump_295 : p1 := by
                        exact assump_153
                      let assump_173 := assump_148 assump_295
                      apply False.elim assump_173
            case inr assump_110 =>
              cases assump_110
              case intro assump_177 assump_178 =>
                have assump_296 : ((p7 ∧ False) → False) := by
                  intro assump_186
                  cases assump_186
                  case intro assump_187 assump_188 =>
                    apply False.elim assump_188
                let assump_185 := assump_5 assump_296
                apply False.elim assump_185
          case inr assump_104 =>
            cases assump_3
            case inl assump_200 =>
              cases assump_200
              case intro assump_202 assump_203 =>
                cases assump_202
                case inl assump_204 =>
                  cases assump_203
                  case intro assump_208 assump_209 =>
                    cases assump_209
                    case inl assump_212 =>
                      have assump_297 : ((p7 ∧ False) → False) := by
                        intro assump_220
                        cases assump_220
                        case intro assump_221 assump_222 =>
                          apply False.elim assump_222
                      let assump_219 := assump_5 assump_297
                      apply False.elim assump_219
                    case inr assump_213 =>
                      have assump_298 : p1 := by
                        exact assump_213
                      let assump_233 := assump_208 assump_298
                      apply False.elim assump_233
                case inr assump_205 =>
                  cases assump_203
                  case intro assump_239 assump_240 =>
                    cases assump_240
                    case inl assump_243 =>
                      have assump_299 : ((p7 ∧ False) → False) := by
                        intro assump_251
                        cases assump_251
                        case intro assump_252 assump_253 =>
                          apply False.elim assump_253
                      let assump_250 := assump_5 assump_299
                      apply False.elim assump_250
                    case inr assump_244 =>
                      have assump_300 : p1 := by
                        exact assump_244
                      let assump_264 := assump_239 assump_300
                      apply False.elim assump_264
            case inr assump_201 =>
              cases assump_201
              case intro assump_268 assump_269 =>
                have assump_301 : ((p7 ∧ False) → False) := by
                  intro assump_277
                  cases assump_277
                  case intro assump_278 assump_279 =>
                    apply False.elim assump_279
                let assump_276 := assump_5 assump_301
                apply False.elim assump_276


variable (p6 p4 p7 p5 p0 p3 : Prop)
theorem file6_18382 : (((((p4 → False) ∨ (p0 ∨ p4)) → ((True ∨ p0) ∨ (p5 → p3))) → False) → ((((True → False) → False) ∧ ((True → True) ∧ (p3 ∨ p7))) → (((p5 ∧ p4) ∨ (p3 ∨ p6)) ∧ ((p3 → True) → False)))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        apply Or.inr
        apply Or.inl
        exact assump_15
      case inr assump_16 =>
        have assump_91 : (((p4 → False) ∨ (p0 ∨ p4)) → ((True ∨ p0) ∨ (p5 → p3))) := by
          intro assump_26
          cases assump_26
          case inl assump_27 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_28 =>
            cases assump_28
            case inl assump_31 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_32 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
        let assump_25 := assump_5 assump_91
        apply False.elim assump_25
  intro assump_40
  cases assump_6
  case intro assump_43 assump_44 =>
    cases assump_44
    case intro assump_47 assump_48 =>
      cases assump_48
      case inl assump_51 =>
        have assump_92 : (((p4 → False) ∨ (p0 ∨ p4)) → ((True ∨ p0) ∨ (p5 → p3))) := by
          intro assump_58
          cases assump_58
          case inl assump_59 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_60 =>
            cases assump_60
            case inl assump_63 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_64 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
        let assump_57 := assump_5 assump_92
        apply False.elim assump_57
      case inr assump_52 =>
        have assump_93 : (((p4 → False) ∨ (p0 ∨ p4)) → ((True ∨ p0) ∨ (p5 → p3))) := by
          intro assump_77
          cases assump_77
          case inl assump_78 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_79 =>
            cases assump_79
            case inl assump_82 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_83 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
        let assump_76 := assump_5 assump_93
        apply False.elim assump_76


variable (p5 p6 p7 p0 p4 p3 : Prop)
theorem file6_21025 : ((((((p4 → p4) → (p7 → False)) ∧ ((p4 ∨ p4) → False)) → False) ∧ ((((p6 → True) ∧ (True ∧ False)) ∧ ((p3 ∨ p0) ∧ (p6 ∧ p3))) ∧ (((p6 → p5) ∨ (p3 → p3)) ∧ ((p7 → False) ∨ (True → False))))) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_27
          case intro assump_30 assump_31 =>
            apply False.elim assump_31


variable (p4 p1 p5 p7 p3 : Prop)
theorem file6_21653 : (((((p4 ∨ p5) → False) ∧ ((True → False) ∧ (False → False))) ∧ (((p1 ∧ p3) ∧ (True ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_22 : True := by
          apply True.intro
        let assump_18 := assump_8 assump_22
        apply False.elim assump_18


variable (p2 p7 p3 p1 p6 p0 p5 : Prop)
theorem file6_22155 : ((((((p0 ∧ p5) ∧ (p1 ∨ p7)) → ((p2 ∧ p6) → (p1 ∨ True))) ∨ (((p3 → p3) → (p2 → p2)) → ((p6 ∧ p1) ∧ (p5 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p0 ∧ p5) ∧ (p1 ∨ p7)) → ((p2 ∧ p6) → (p1 ∨ True))) ∨ (((p3 → p3) → (p2 → p2)) → ((p6 ∧ p1) ∧ (p5 ∨ p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case inl assump_21 =>
            apply Or.inl
            exact assump_21
          case inr assump_22 =>
            apply Or.inr
            apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p0 p4 p5 p6 p7 p2 p3 p1 : Prop)
theorem file6_23008 : (((((True → False) ∧ (p1 → False)) ∨ ((p6 ∧ p7) → (p5 → False))) ∧ (((False → False) → False) ∧ ((p7 ∨ p3) ∧ (False → False)))) → ((((p2 ∨ p5) ∧ (p4 ∨ p1)) → False) ∨ (((p1 ∨ p0) ∨ (p3 → False)) ∨ ((False ∧ p0) → False)))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_11
        case intro assump_20 assump_21 =>
          cases assump_21
          case intro assump_24 assump_25 =>
            cases assump_24
            case inl assump_26 =>
              apply Or.inl
              intro assump_32
              cases assump_32
              case intro assump_33 assump_34 =>
                cases assump_33
                case inl assump_35 =>
                  cases assump_34
                  case inl assump_39 =>
                    have assump_314 : (False → False) := by
                      intro assump_48
                      apply False.elim assump_48
                    let assump_47 := assump_20 assump_314
                    apply False.elim assump_47
                  case inr assump_40 =>
                    have assump_315 : (False → False) := by
                      intro assump_61
                      apply False.elim assump_61
                    let assump_60 := assump_20 assump_315
                    apply False.elim assump_60
                case inr assump_36 =>
                  cases assump_34
                  case inl assump_69 =>
                    have assump_316 : (False → False) := by
                      intro assump_78
                      apply False.elim assump_78
                    let assump_77 := assump_20 assump_316
                    apply False.elim assump_77
                  case inr assump_70 =>
                    have assump_317 : (False → False) := by
                      intro assump_91
                      apply False.elim assump_91
                    let assump_90 := assump_20 assump_317
                    apply False.elim assump_90
            case inr assump_27 =>
              apply Or.inl
              intro assump_101
              cases assump_101
              case intro assump_102 assump_103 =>
                cases assump_102
                case inl assump_104 =>
                  cases assump_103
                  case inl assump_108 =>
                    have assump_318 : (False → False) := by
                      intro assump_117
                      apply False.elim assump_117
                    let assump_116 := assump_20 assump_318
                    apply False.elim assump_116
                  case inr assump_109 =>
                    have assump_319 : (False → False) := by
                      intro assump_130
                      apply False.elim assump_130
                    let assump_129 := assump_20 assump_319
                    apply False.elim assump_129
                case inr assump_105 =>
                  cases assump_103
                  case inl assump_138 =>
                    have assump_320 : (False → False) := by
                      intro assump_147
                      apply False.elim assump_147
                    let assump_146 := assump_20 assump_320
                    apply False.elim assump_146
                  case inr assump_139 =>
                    have assump_321 : (False → False) := by
                      intro assump_160
                      apply False.elim assump_160
                    let assump_159 := assump_20 assump_321
                    apply False.elim assump_159
    case inr assump_13 =>
      cases assump_11
      case intro assump_168 assump_169 =>
        cases assump_169
        case intro assump_172 assump_173 =>
          cases assump_172
          case inl assump_174 =>
            apply Or.inl
            intro assump_180
            cases assump_180
            case intro assump_181 assump_182 =>
              cases assump_181
              case inl assump_183 =>
                cases assump_182
                case inl assump_187 =>
                  have assump_322 : (False → False) := by
                    intro assump_196
                    apply False.elim assump_196
                  let assump_195 := assump_168 assump_322
                  apply False.elim assump_195
                case inr assump_188 =>
                  have assump_323 : (False → False) := by
                    intro assump_209
                    apply False.elim assump_209
                  let assump_208 := assump_168 assump_323
                  apply False.elim assump_208
              case inr assump_184 =>
                cases assump_182
                case inl assump_217 =>
                  have assump_324 : (False → False) := by
                    intro assump_226
                    apply False.elim assump_226
                  let assump_225 := assump_168 assump_324
                  apply False.elim assump_225
                case inr assump_218 =>
                  have assump_325 : (False → False) := by
                    intro assump_239
                    apply False.elim assump_239
                  let assump_238 := assump_168 assump_325
                  apply False.elim assump_238
          case inr assump_175 =>
            apply Or.inl
            intro assump_249
            cases assump_249
            case intro assump_250 assump_251 =>
              cases assump_250
              case inl assump_252 =>
                cases assump_251
                case inl assump_256 =>
                  have assump_326 : (False → False) := by
                    intro assump_265
                    apply False.elim assump_265
                  let assump_264 := assump_168 assump_326
                  apply False.elim assump_264
                case inr assump_257 =>
                  have assump_327 : (False → False) := by
                    intro assump_278
                    apply False.elim assump_278
                  let assump_277 := assump_168 assump_327
                  apply False.elim assump_277
              case inr assump_253 =>
                cases assump_251
                case inl assump_286 =>
                  have assump_328 : (False → False) := by
                    intro assump_295
                    apply False.elim assump_295
                  let assump_294 := assump_168 assump_328
                  apply False.elim assump_294
                case inr assump_287 =>
                  have assump_329 : (False → False) := by
                    intro assump_308
                    apply False.elim assump_308
                  let assump_307 := assump_168 assump_329
                  apply False.elim assump_307


variable (p7 p3 p0 p6 p1 p4 p2 : Prop)
theorem file6_29841 : (((((False ∧ p4) → False) ∨ ((p0 ∧ p2) ∨ (p7 → False))) → (((False ∧ p1) ∧ (p4 → False)) ∨ ((p6 → p6) → False))) → ((((p4 ∧ False) → False) ∨ ((p0 → False) ∨ (p3 ∨ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_121 : (((False ∧ p4) → False) ∨ ((p0 ∧ p2) ∨ (p7 → False))) := by
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    let assump_9 := assump_1 assump_121
    cases assump_9
    case inl assump_16 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
    case inr assump_17 =>
      have assump_122 : (p6 → p6) := by
        intro assump_27
        exact assump_27
      let assump_26 := assump_17 assump_122
      apply False.elim assump_26
  case inr assump_4 =>
    cases assump_4
    case inl assump_33 =>
      have assump_123 : (((False ∧ p4) → False) ∨ ((p0 ∧ p2) ∨ (p7 → False))) := by
        apply Or.inl
        intro assump_40
        cases assump_40
        case intro assump_41 assump_42 =>
          apply False.elim assump_41
      let assump_39 := assump_1 assump_123
      cases assump_39
      case inl assump_46 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            apply False.elim assump_50
      case inr assump_47 =>
        have assump_124 : (p6 → p6) := by
          intro assump_57
          exact assump_57
        let assump_56 := assump_47 assump_124
        apply False.elim assump_56
    case inr assump_34 =>
      cases assump_34
      case inl assump_63 =>
        have assump_125 : (((False ∧ p4) → False) ∨ ((p0 ∧ p2) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_70
          cases assump_70
          case intro assump_71 assump_72 =>
            apply False.elim assump_71
        let assump_69 := assump_1 assump_125
        cases assump_69
        case inl assump_76 =>
          cases assump_76
          case intro assump_78 assump_79 =>
            cases assump_78
            case intro assump_80 assump_81 =>
              apply False.elim assump_80
        case inr assump_77 =>
          have assump_126 : (p6 → p6) := by
            intro assump_87
            exact assump_87
          let assump_86 := assump_77 assump_126
          apply False.elim assump_86
      case inr assump_64 =>
        have assump_127 : (((False ∧ p4) → False) ∨ ((p0 ∧ p2) ∨ (p7 → False))) := by
          apply Or.inl
          intro assump_98
          cases assump_98
          case intro assump_99 assump_100 =>
            apply False.elim assump_99
        let assump_97 := assump_1 assump_127
        cases assump_97
        case inl assump_104 =>
          cases assump_104
          case intro assump_106 assump_107 =>
            cases assump_106
            case intro assump_108 assump_109 =>
              apply False.elim assump_108
        case inr assump_105 =>
          have assump_128 : (p6 → p6) := by
            intro assump_115
            exact assump_115
          let assump_114 := assump_105 assump_128
          apply False.elim assump_114


variable (p4 p5 p6 p7 p2 p0 p1 p3 : Prop)
theorem file6_33204 : ((((((p1 ∧ p0) → (p5 ∨ p7)) ∧ ((p5 → False) ∧ (p6 ∨ p4))) → (((p5 ∨ True) ∨ (p5 → p1)) → ((True → p3) ∧ (p6 ∧ p6)))) ∧ ((((p2 ∧ p7) → (True ∨ p5)) ∨ ((p1 ∧ p0) → (True ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p2 ∧ p7) → (True ∨ p5)) ∨ ((p1 ∧ p0) → (True ∨ False))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p5 p2 p4 p7 p1 : Prop)
theorem file6_33835 : (((((p7 ∧ p7) ∧ (p2 ∧ p4)) → False) ∧ (((p7 ∨ p1) ∨ (p7 ∧ p4)) → ((p2 → False) ∧ (p5 ∧ p7)))) → ((((p5 ∨ p1) ∨ (False → False)) → False) → False)) := by
  intro assump_38
  intro assump_39
  cases assump_38
  case intro assump_42 assump_43 =>
    have assump_57 : ((p5 ∨ p1) ∨ (False → False)) := by
      apply Or.inr
      intro assump_51
      apply False.elim assump_51
    let assump_50 := assump_39 assump_57
    apply False.elim assump_50


variable (p7 p4 p6 p1 : Prop)
theorem file6_34335 : (((((p1 → False) → (p1 → p7)) ∨ ((p1 → False) → False)) ∨ (((p6 ∨ p6) ∨ (False → False)) ∨ ((False → p6) ∨ (p7 → False)))) ∨ ((((True ∨ p6) ∧ (p4 → p6)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : p1 := by
    exact assump_2
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p5 p3 p6 p4 p2 p7 p1 : Prop)
theorem file6_34767 : ((((((p3 → True) → False) → False) → False) ∨ ((((p4 ∨ p5) ∨ (p1 → False)) ∧ ((p1 ∧ p7) ∧ (False ∧ p2))) ∧ (((p2 → False) → False) → ((p7 ∧ p1) ∧ (p7 ∧ p6))))) → False) := by
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    have assump_78 : (((p3 → True) → False) → False) := by
      intro assump_17
      have assump_79 : (p3 → True) := by
        intro assump_21
        apply True.intro
      let assump_20 := assump_17 assump_79
      apply False.elim assump_20
    let assump_16 := assump_12 assump_78
    apply False.elim assump_16
  case inr assump_13 =>
    cases assump_13
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_32
          case inl assump_34 =>
            cases assump_31
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                cases assump_39
                case intro assump_46 assump_47 =>
                  apply False.elim assump_46
          case inr assump_35 =>
            cases assump_31
            case intro assump_52 assump_53 =>
              cases assump_52
              case intro assump_54 assump_55 =>
                cases assump_53
                case intro assump_60 assump_61 =>
                  apply False.elim assump_60
        case inr assump_33 =>
          cases assump_31
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              cases assump_67
              case intro assump_74 assump_75 =>
                apply False.elim assump_74


variable (p6 p0 p1 p4 p7 p2 p3 p5 : Prop)
theorem file6_36528 : (((((p5 ∨ False) → (p7 ∨ False)) ∧ ((p0 ∨ p3) → (p4 ∧ p2))) ∨ (((p3 → False) → False) → ((p1 ∧ p1) → False))) → ((((True ∨ p6) → (False ∧ False)) → ((p6 ∨ p3) ∧ (p2 ∨ p5))) ∨ (((p7 → p5) ∧ (p0 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      apply And.intro
      have assump_42 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_13 := assump_10 assump_42
      let assump_14 := And.left assump_13
      apply False.elim assump_14
      have assump_43 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_20 := assump_10 assump_43
      let assump_21 := And.left assump_20
      apply False.elim assump_21
  case inr assump_3 =>
    apply Or.inl
    intro assump_27
    apply And.intro
    have assump_44 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_30 := assump_27 assump_44
    let assump_31 := And.left assump_30
    apply False.elim assump_31
    have assump_45 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_37 := assump_27 assump_45
    let assump_38 := And.left assump_37
    apply False.elim assump_38


variable (p3 p1 p6 p4 p7 p2 p5 p0 : Prop)
theorem file6_37865 : (((((False → False) → False) → False) → False) → ((((p2 ∧ p3) → (p0 ∧ p1)) → False) ∧ (((p2 → p2) ∧ (p5 → p0)) → ((p7 → p7) ∧ (p6 → p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_58 : (((False → False) → False) → False) := by
    intro assump_8
    have assump_59 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_8 assump_59
    apply False.elim assump_11
  let assump_7 := assump_1 assump_58
  apply False.elim assump_7
  intro assump_21
  apply And.intro
  intro assump_22
  cases assump_21
  case intro assump_25 assump_26 =>
    exact assump_22
  intro assump_33
  cases assump_21
  case intro assump_36 assump_37 =>
    have assump_60 : (((False → False) → False) → False) := by
      intro assump_45
      have assump_61 : (False → False) := by
        intro assump_49
        apply False.elim assump_49
      let assump_48 := assump_45 assump_61
      apply False.elim assump_48
    let assump_44 := assump_1 assump_60
    apply False.elim assump_44


variable (p1 p6 p2 p4 p7 p5 p3 p0 : Prop)
theorem file6_38979 : (((((p7 ∨ p0) → (False ∨ p3)) → False) → (((p3 ∧ p3) → (p0 ∧ p2)) ∨ ((p7 ∨ p2) → False))) ∨ ((((p7 ∧ p5) → (p6 → p0)) ∨ ((p2 ∨ p5) ∨ (p4 → p0))) ∨ (((p6 ∧ p5) ∧ (p5 → p3)) ∧ ((False → False) ∧ (p3 ∧ p1))))) := by
  apply Or.inl
  intro assump_39
  apply Or.inl
  intro assump_42
  apply And.intro
  cases assump_42
  case intro assump_43 assump_44 =>
    have assump_81 : ((p7 ∨ p0) → (False ∨ p3)) := by
      intro assump_52
      cases assump_52
      case inl assump_53 =>
        apply Or.inr
        exact assump_44
      case inr assump_54 =>
        apply Or.inr
        exact assump_44
    let assump_51 := assump_39 assump_81
    apply False.elim assump_51
  cases assump_42
  case intro assump_62 assump_63 =>
    have assump_82 : ((p7 ∨ p0) → (False ∨ p3)) := by
      intro assump_71
      cases assump_71
      case inl assump_72 =>
        apply Or.inr
        exact assump_63
      case inr assump_73 =>
        apply Or.inr
        exact assump_63
    let assump_70 := assump_39 assump_82
    apply False.elim assump_70


variable (p5 p0 p3 p2 p7 p1 p6 : Prop)
theorem file6_40079 : ((((((p5 ∨ True) ∧ (p0 ∨ p1)) ∨ ((False → True) ∧ (p5 ∧ p5))) → False) ∧ ((((p6 → p6) ∧ (p2 ∧ p7)) ∧ ((p5 ∧ p5) → False)) ∧ (((p1 → p7) ∨ (p3 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            have assump_31 : ((p1 → p7) ∨ (p3 → True)) := by
              apply Or.inl
              intro assump_25
              exact assump_15
            let assump_24 := assump_7 assump_31
            apply False.elim assump_24


variable (p6 p4 p1 p5 p2 p0 : Prop)
theorem file6_40868 : ((((((p5 → p5) → False) → ((False → p5) → (False ∨ p1))) ∧ (((p6 ∨ p6) ∨ (p0 ∧ p2)) → ((p4 ∨ True) ∨ (p1 ∨ p4)))) → False) → False) := by
  intro assump_10
  have assump_45 : ((((p5 → p5) → False) → ((False → p5) → (False ∨ p1))) ∧ (((p6 ∨ p6) ∨ (p0 ∧ p2)) → ((p4 ∨ True) ∨ (p1 ∨ p4)))) := by
    apply And.intro
    intro assump_14
    intro assump_15
    have assump_46 : (p5 → p5) := by
      intro assump_21
      exact assump_21
    let assump_20 := assump_14 assump_46
    apply False.elim assump_20
    intro assump_27
    cases assump_27
    case inl assump_28 =>
      cases assump_28
      case inl assump_30 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_31 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_29 =>
      cases assump_29
      case intro assump_36 assump_37 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_13 := assump_10 assump_45
  apply False.elim assump_13


variable (p5 p3 p2 p0 p7 p6 p1 p4 : Prop)
theorem file6_41941 : (((((True ∨ p0) ∧ (p3 ∧ p2)) ∨ ((p7 ∨ p3) ∧ (p2 ∧ p1))) ∧ (((p5 → p6) → (p6 ∨ p2)) → False)) → ((((p5 → False) ∧ (p4 → False)) ∨ ((p5 ∨ True) → (p1 → p1))) → (((p7 ∨ p1) → False) → False))) := by
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case inl assump_16 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_11
      case intro assump_24 assump_25 =>
        cases assump_24
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              cases assump_29
              case intro assump_34 assump_35 =>
                have assump_186 : ((p5 → p6) → (p6 ∨ p2)) := by
                  intro assump_43
                  apply Or.inr
                  exact assump_35
                let assump_42 := assump_25 assump_186
                apply False.elim assump_42
            case inr assump_31 =>
              cases assump_29
              case intro assump_51 assump_52 =>
                have assump_187 : ((p5 → p6) → (p6 ∨ p2)) := by
                  intro assump_60
                  apply Or.inr
                  exact assump_52
                let assump_59 := assump_25 assump_187
                apply False.elim assump_59
        case inr assump_27 =>
          cases assump_27
          case intro assump_66 assump_67 =>
            cases assump_66
            case inl assump_68 =>
              cases assump_67
              case intro assump_72 assump_73 =>
                have assump_188 : ((p5 → p6) → (p6 ∨ p2)) := by
                  intro assump_81
                  apply Or.inr
                  exact assump_72
                let assump_80 := assump_25 assump_188
                apply False.elim assump_80
            case inr assump_69 =>
              cases assump_67
              case intro assump_89 assump_90 =>
                have assump_189 : ((p5 → p6) → (p6 ∨ p2)) := by
                  intro assump_98
                  apply Or.inr
                  exact assump_89
                let assump_97 := assump_25 assump_189
                apply False.elim assump_97
  case inr assump_17 =>
    cases assump_11
    case intro assump_106 assump_107 =>
      cases assump_106
      case inl assump_108 =>
        cases assump_108
        case intro assump_110 assump_111 =>
          cases assump_110
          case inl assump_112 =>
            cases assump_111
            case intro assump_116 assump_117 =>
              have assump_190 : ((p5 → p6) → (p6 ∨ p2)) := by
                intro assump_125
                apply Or.inr
                exact assump_117
              let assump_124 := assump_107 assump_190
              apply False.elim assump_124
          case inr assump_113 =>
            cases assump_111
            case intro assump_133 assump_134 =>
              have assump_191 : ((p5 → p6) → (p6 ∨ p2)) := by
                intro assump_142
                apply Or.inr
                exact assump_134
              let assump_141 := assump_107 assump_191
              apply False.elim assump_141
      case inr assump_109 =>
        cases assump_109
        case intro assump_148 assump_149 =>
          cases assump_148
          case inl assump_150 =>
            cases assump_149
            case intro assump_154 assump_155 =>
              have assump_192 : ((p5 → p6) → (p6 ∨ p2)) := by
                intro assump_163
                apply Or.inr
                exact assump_154
              let assump_162 := assump_107 assump_192
              apply False.elim assump_162
          case inr assump_151 =>
            cases assump_149
            case intro assump_171 assump_172 =>
              have assump_193 : ((p5 → p6) → (p6 ∨ p2)) := by
                intro assump_180
                apply Or.inr
                exact assump_171
              let assump_179 := assump_107 assump_193
              apply False.elim assump_179


variable (p1 p3 p7 p0 p4 p6 : Prop)
theorem file6_45990 : (((((p0 → p6) → (p0 ∨ p4)) ∧ ((p0 → p0) → False)) → False) ∨ ((((p0 ∧ p0) → False) → False) ∧ (((p0 → p1) → (p1 ∧ p1)) → ((p7 ∨ p3) ∨ (p0 → p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (p0 → p0) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p3 p4 p5 p2 p0 p1 : Prop)
theorem file6_46438 : (((((True → False) ∧ (p3 → True)) → False) → False) → ((((True → False) ∧ (p6 → False)) → ((p6 → False) → (p4 ∨ p1))) ∧ (((p5 ∧ p3) → False) ∨ ((p0 ∧ p1) ∧ (p4 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_58 : (((True → False) ∧ (p3 → True)) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        have assump_59 : True := by
          apply True.intro
        let assump_23 := assump_16 assump_59
        apply False.elim assump_23
    let assump_14 := assump_1 assump_58
    apply False.elim assump_14
  apply Or.inl
  intro assump_32
  cases assump_32
  case intro assump_33 assump_34 =>
    have assump_60 : (((True → False) ∧ (p3 → True)) → False) := by
      intro assump_42
      cases assump_42
      case intro assump_43 assump_44 =>
        have assump_61 : True := by
          apply True.intro
        let assump_51 := assump_43 assump_61
        apply False.elim assump_51
    let assump_41 := assump_1 assump_60
    apply False.elim assump_41


variable (p2 p5 p6 : Prop)
theorem file6_47604 : ((((((False ∨ False) ∨ (False → p2)) ∧ ((p5 ∨ True) → False)) → (((True ∧ p5) → (p6 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False ∨ False) ∨ (False → p2)) ∧ ((p5 ∨ True) → False)) → (((True ∧ p5) → (p6 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          apply False.elim assump_14
      case inr assump_12 =>
        have assump_31 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_23 := assump_10 assump_31
        apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p0 p3 p1 p4 p2 : Prop)
theorem file6_48500 : (((((True ∧ False) → False) → False) → False) ∨ ((((p1 → p2) ∨ (p2 → p4)) ∧ ((p0 ∧ True) → False)) → (((p1 ∨ p4) ∨ (p4 → p3)) ∨ ((False → False) ∨ (p4 → p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p6 p5 p0 : Prop)
theorem file6_48974 : ((((((p6 ∨ p2) ∧ (p5 → False)) → False) ∨ (((p0 ∨ p0) → False) → False)) ∧ ((((True → False) → False) ∨ ((p5 → p6) ∧ (p5 ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : (((True → False) → False) ∨ ((p5 → p6) ∧ (p5 ∨ p0))) := by
        apply Or.inl
        intro assump_11
        have assump_37 : True := by
          apply True.intro
        let assump_14 := assump_11 assump_37
        apply False.elim assump_14
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_38 : (((True → False) → False) ∨ ((p5 → p6) ∧ (p5 ∨ p0))) := by
        apply Or.inl
        intro assump_26
        have assump_39 : True := by
          apply True.intro
        let assump_29 := assump_26 assump_39
        apply False.elim assump_29
      let assump_25 := assump_3 assump_38
      apply False.elim assump_25


variable (p7 p3 p6 p5 p4 p2 : Prop)
theorem file6_50015 : ((((((p5 → p4) ∧ (p2 ∨ p3)) ∧ ((p7 ∧ p6) ∧ (p2 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p5 → p4) ∧ (p2 ∨ p3)) ∧ ((p7 ∧ p6) ∧ (p2 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
        case inr assump_13 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              cases assump_33
              case intro assump_40 assump_41 =>
                apply False.elim assump_41
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p1 p5 p4 p2 p7 p3 p6 : Prop)
theorem file6_51085 : (((((p6 → p2) → False) ∧ ((p2 → p4) ∧ (p7 ∧ False))) → (((p4 → False) ∧ (p1 ∧ p5)) ∨ ((p3 ∨ p7) ∨ (p4 → p1)))) ∧ ((((p4 ∧ p2) → False) ∧ ((p3 ∧ True) ∧ (True → False))) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        have assump_35 : True := by
          apply True.intro
        let assump_31 := assump_22 assump_35
        apply False.elim assump_31


variable (p3 p5 : Prop)
theorem file6_51890 : ((((((p5 → False) → (p5 → p3)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 → False) → (p5 → p3)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p5 → False) → (p5 → p3)) := by
      intro assump_9
      intro assump_10
      have assump_27 : p5 := by
        exact assump_10
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p0 p4 p7 p2 p1 p3 p5 : Prop)
theorem file6_52499 : (((((p2 ∨ p3) ∧ (False ∨ p7)) → ((True ∨ p6) ∨ (p5 → p4))) ∨ (((False → False) ∧ (p6 ∨ p1)) → ((True ∧ p0) ∧ (p1 → False)))) ∨ ((((p6 ∧ p4) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      cases assump_3
      case inl assump_16 =>
        apply False.elim assump_16
      case inr assump_17 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p1 p7 p4 p2 p0 p6 p3 p5 : Prop)
theorem file6_53261 : ((((((p6 → False) ∧ (p7 → False)) → ((p1 → False) ∨ (p6 → p0))) → (((p5 ∧ p6) ∧ (p0 ∨ p2)) → False)) ∧ ((((p4 → p0) → (p1 → p3)) ∨ ((p0 → False) ∧ (p1 ∨ p3))) ∧ (((p3 ∧ p7) → (p7 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_61 : ((p3 ∧ p7) → (p7 ∨ p0)) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply Or.inl
            exact assump_17
        let assump_14 := assump_7 assump_61
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_25 assump_26 =>
          cases assump_26
          case inl assump_29 =>
            have assump_62 : ((p3 ∧ p7) → (p7 ∨ p0)) := by
              intro assump_36
              cases assump_36
              case intro assump_37 assump_38 =>
                apply Or.inl
                exact assump_38
            let assump_35 := assump_7 assump_62
            apply False.elim assump_35
          case inr assump_30 =>
            have assump_63 : ((p3 ∧ p7) → (p7 ∨ p0)) := by
              intro assump_51
              cases assump_51
              case intro assump_52 assump_53 =>
                apply Or.inl
                exact assump_53
            let assump_50 := assump_7 assump_63
            apply False.elim assump_50


variable (p6 p3 p1 p7 p4 p5 p2 p0 : Prop)
theorem file6_54805 : (((((p7 ∨ p2) ∧ (False ∧ p5)) → False) ∨ (((p4 ∨ p6) ∧ (p7 → p7)) ∧ ((p4 → p3) ∧ (p0 ∨ p7)))) ∨ ((((p1 → False) ∧ (p1 → p0)) ∧ ((p3 ∧ True) ∨ (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p4 p6 p0 p7 p3 p2 p5 : Prop)
theorem file6_55397 : (((((False ∧ True) → (p2 ∨ True)) → False) → (((p0 → p3) → False) ∨ ((p7 → p3) → False))) ∨ ((((p5 → p4) ∨ (False → False)) → False) ∧ (((p6 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_17 : ((False ∧ True) → (p2 ∨ True)) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_8 := assump_1 assump_17
  apply False.elim assump_8


variable (p3 p5 p6 p7 p1 p0 : Prop)
theorem file6_55927 : (((((True ∨ False) → False) ∧ ((p6 → p1) ∨ (False → False))) → (((p1 → False) → False) → ((p6 ∨ True) → False))) → ((((p3 → p0) ∧ (p7 ∨ p3)) ∨ ((p0 ∧ p5) → False)) → (((True ∧ p7) ∧ (p7 ∧ p6)) → ((p7 ∨ p1) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        cases assump_2
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              apply Or.inl
              apply Or.inl
              exact assump_24
            case inr assump_25 =>
              apply Or.inl
              apply Or.inl
              exact assump_12
        case inr assump_19 =>
          apply Or.inl
          apply Or.inl
          exact assump_12


variable (p7 p2 p5 p3 p1 p6 : Prop)
theorem file6_56925 : ((((((p2 ∨ True) → (p7 → p1)) → False) ∧ (((p6 → False) ∧ (False ∨ p1)) ∧ ((False → p5) → False))) ∧ ((((p1 ∨ p2) ∧ (p3 → p7)) ∧ ((p3 → p6) ∧ (p5 ∧ False))) ∨ (((p6 → p7) ∧ (p6 → p6)) ∨ ((p3 ∨ p7) → (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            cases assump_3
            case inl assump_22 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_25
                    case intro assump_34 assump_35 =>
                      cases assump_35
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_39
                  case inr assump_29 =>
                    cases assump_25
                    case intro assump_48 assump_49 =>
                      cases assump_49
                      case intro assump_52 assump_53 =>
                        apply False.elim assump_53
            case inr assump_23 =>
              cases assump_23
              case inl assump_58 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  have assump_85 : (False → p5) := by
                    intro assump_69
                    apply False.elim assump_69
                  let assump_68 := assump_9 assump_85
                  apply False.elim assump_68
              case inr assump_59 =>
                have assump_86 : (False → p5) := by
                  intro assump_79
                  apply False.elim assump_79
                let assump_78 := assump_9 assump_86
                apply False.elim assump_78


variable (p3 p0 p4 p6 p2 : Prop)
theorem file6_59074 : (((((False → False) → False) → ((p4 ∧ p6) → False)) ∨ (((p3 ∨ p2) ∨ (p2 → p6)) ∧ ((p4 ∧ False) ∧ (p3 → p0)))) ∨ ((((p6 ∨ p3) ∨ (False → False)) → ((p2 ∨ p6) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_1 assump_18
    apply False.elim assump_11


variable (p0 p3 p6 p7 p4 p5 : Prop)
theorem file6_59601 : ((((((p3 → False) → False) → ((p4 ∨ p5) → (p4 ∨ True))) ∨ (((p0 ∧ p0) → (p5 → False)) ∧ ((p6 ∧ p5) ∧ (p7 → p7)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p3 → False) → False) → ((p4 ∨ p5) → (p4 ∨ True))) ∨ (((p0 ∧ p0) → (p5 → False)) ∧ ((p6 ∧ p5) ∧ (p7 → p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      exact assump_7
    case inr assump_8 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p7 p2 p0 p1 p4 : Prop)
theorem file6_60224 : ((((((False → False) ∧ (p0 → p1)) → False) → (((p0 ∧ p1) ∧ (p2 ∨ p3)) → ((p0 → False) → (p4 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_91 : ((((False → False) ∧ (p0 → p1)) → False) → (((p0 ∧ p1) ∧ (p2 ∨ p3)) → ((p0 → False) → (p4 ∧ p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          have assump_92 : ((False → False) ∧ (p0 → p1)) := by
            apply And.intro
            intro assump_25
            apply False.elim assump_25
            intro assump_28
            exact assump_13
          let assump_24 := assump_5 assump_92
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_93 : ((False → False) ∧ (p0 → p1)) := by
            apply And.intro
            intro assump_39
            apply False.elim assump_39
            intro assump_42
            exact assump_13
          let assump_38 := assump_5 assump_93
          apply False.elim assump_38
    cases assump_6
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_51
        case inl assump_58 =>
          have assump_94 : ((False → False) ∧ (p0 → p1)) := by
            apply And.intro
            intro assump_65
            apply False.elim assump_65
            intro assump_68
            exact assump_53
          let assump_64 := assump_5 assump_94
          apply False.elim assump_64
        case inr assump_59 =>
          have assump_95 : ((False → False) ∧ (p0 → p1)) := by
            apply And.intro
            intro assump_79
            apply False.elim assump_79
            intro assump_82
            exact assump_53
          let assump_78 := assump_5 assump_95
          apply False.elim assump_78
  let assump_4 := assump_1 assump_91
  apply False.elim assump_4


variable (p6 p7 p3 p1 p2 : Prop)
theorem file6_62283 : (((((p6 ∧ p3) ∨ (False → False)) ∨ ((p1 ∧ p6) ∨ (p7 → False))) → False) → ((((p6 ∨ p1) → False) → False) → (((True → p3) ∧ (p2 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_21 : (((p6 ∧ p3) ∨ (False → False)) ∨ ((p1 ∧ p6) ∨ (p7 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_1 assump_21
    apply False.elim assump_14


variable (p3 p6 p2 p5 p4 : Prop)
theorem file6_62848 : ((((((True ∨ False) → (p6 ∨ p3)) → False) → (((p4 → p4) → (False → p5)) ∨ ((p5 ∨ p2) ∧ (p4 → p6)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ False) → (p6 ∨ p3)) → False) → (((p4 → p4) → (False → p5)) ∨ ((p5 ∨ p2) ∧ (p4 → p6)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p7 p0 p2 p4 p6 : Prop)
theorem file6_63341 : ((((((p0 → False) → (p7 ∨ True)) → ((False → p6) ∨ (p0 ∨ p7))) ∧ (((p4 → p7) ∧ (False ∨ p4)) → False)) ∧ ((((False ∨ p2) → (p0 → True)) ∨ ((p3 ∨ p4) → False)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_22 : (((False ∨ p2) → (p0 → True)) ∨ ((p3 ∨ p4) → False)) := by
        apply Or.inl
        intro assump_17
        intro assump_18
        apply True.intro
      let assump_16 := assump_7 assump_22
      apply False.elim assump_16


variable (p7 p1 p5 p6 p2 p3 p0 : Prop)
theorem file6_63962 : ((((((False → False) → (False → False)) ∧ ((False ∧ True) ∧ (False → False))) ∧ (((p2 → False) ∨ (p6 ∨ p3)) ∧ ((p5 → p5) → False))) ∧ ((((p0 ∨ p0) → (p0 → p5)) → ((p7 → False) ∨ (p6 ∧ p1))) ∨ (((p1 ∨ p5) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p3 p6 p4 p2 p7 p1 : Prop)
theorem file6_64617 : (((((p1 → p6) → False) ∨ ((p7 ∨ True) → (p4 → False))) → False) → ((((True → False) ∧ (p1 ∨ p3)) → False) ∨ (((p3 ∨ p2) ∨ (p6 → p2)) ∨ ((p1 ∧ False) → (p7 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_25 : True := by
        apply True.intro
      let assump_14 := assump_5 assump_25
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_26 : True := by
        apply True.intro
      let assump_21 := assump_5 assump_26
      apply False.elim assump_21


variable (p5 p1 p4 p7 p0 p6 p3 : Prop)
theorem file6_65292 : (((((p3 ∧ p1) ∨ (p6 → p3)) ∧ ((p6 ∨ p6) ∧ (p1 ∨ p1))) ∧ (((False ∧ p7) → (p0 ∨ p4)) → ((p3 ∧ False) → False))) → ((((p6 → p1) → False) ∧ ((p5 → p6) ∨ (p4 ∨ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              cases assump_14
              case intro assump_23 assump_24 =>
                cases assump_23
                case inl assump_25 =>
                  cases assump_24
                  case inl assump_29 =>
                    have assump_683 : (p6 → p1) := by
                      intro assump_48
                      exact assump_29
                    let assump_47 := assump_3 assump_683
                    apply False.elim assump_47
                  case inr assump_30 =>
                    have assump_684 : (p6 → p1) := by
                      intro assump_71
                      exact assump_30
                    let assump_70 := assump_3 assump_684
                    apply False.elim assump_70
                case inr assump_26 =>
                  cases assump_24
                  case inl assump_79 =>
                    have assump_685 : (p6 → p1) := by
                      intro assump_98
                      exact assump_79
                    let assump_97 := assump_3 assump_685
                    apply False.elim assump_97
                  case inr assump_80 =>
                    have assump_686 : (p6 → p1) := by
                      intro assump_121
                      exact assump_80
                    let assump_120 := assump_3 assump_686
                    apply False.elim assump_120
          case inr assump_16 =>
            cases assump_14
            case intro assump_129 assump_130 =>
              cases assump_129
              case inl assump_131 =>
                cases assump_130
                case inl assump_135 =>
                  have assump_687 : (p6 → p1) := by
                    intro assump_154
                    exact assump_135
                  let assump_153 := assump_3 assump_687
                  apply False.elim assump_153
                case inr assump_136 =>
                  have assump_688 : (p6 → p1) := by
                    intro assump_177
                    exact assump_136
                  let assump_176 := assump_3 assump_688
                  apply False.elim assump_176
              case inr assump_132 =>
                cases assump_130
                case inl assump_185 =>
                  have assump_689 : (p6 → p1) := by
                    intro assump_204
                    exact assump_185
                  let assump_203 := assump_3 assump_689
                  apply False.elim assump_203
                case inr assump_186 =>
                  have assump_690 : (p6 → p1) := by
                    intro assump_227
                    exact assump_186
                  let assump_226 := assump_3 assump_690
                  apply False.elim assump_226
    case inr assump_8 =>
      cases assump_8
      case inl assump_233 =>
        cases assump_1
        case intro assump_237 assump_238 =>
          cases assump_237
          case intro assump_239 assump_240 =>
            cases assump_239
            case inl assump_241 =>
              cases assump_241
              case intro assump_243 assump_244 =>
                cases assump_240
                case intro assump_249 assump_250 =>
                  cases assump_249
                  case inl assump_251 =>
                    cases assump_250
                    case inl assump_255 =>
                      have assump_691 : (p6 → p1) := by
                        intro assump_274
                        exact assump_255
                      let assump_273 := assump_3 assump_691
                      apply False.elim assump_273
                    case inr assump_256 =>
                      have assump_692 : (p6 → p1) := by
                        intro assump_297
                        exact assump_256
                      let assump_296 := assump_3 assump_692
                      apply False.elim assump_296
                  case inr assump_252 =>
                    cases assump_250
                    case inl assump_305 =>
                      have assump_693 : (p6 → p1) := by
                        intro assump_324
                        exact assump_305
                      let assump_323 := assump_3 assump_693
                      apply False.elim assump_323
                    case inr assump_306 =>
                      have assump_694 : (p6 → p1) := by
                        intro assump_347
                        exact assump_306
                      let assump_346 := assump_3 assump_694
                      apply False.elim assump_346
            case inr assump_242 =>
              cases assump_240
              case intro assump_355 assump_356 =>
                cases assump_355
                case inl assump_357 =>
                  cases assump_356
                  case inl assump_361 =>
                    have assump_695 : (p6 → p1) := by
                      intro assump_380
                      exact assump_361
                    let assump_379 := assump_3 assump_695
                    apply False.elim assump_379
                  case inr assump_362 =>
                    have assump_696 : (p6 → p1) := by
                      intro assump_403
                      exact assump_362
                    let assump_402 := assump_3 assump_696
                    apply False.elim assump_402
                case inr assump_358 =>
                  cases assump_356
                  case inl assump_411 =>
                    have assump_697 : (p6 → p1) := by
                      intro assump_430
                      exact assump_411
                    let assump_429 := assump_3 assump_697
                    apply False.elim assump_429
                  case inr assump_412 =>
                    have assump_698 : (p6 → p1) := by
                      intro assump_453
                      exact assump_412
                    let assump_452 := assump_3 assump_698
                    apply False.elim assump_452
      case inr assump_234 =>
        cases assump_1
        case intro assump_461 assump_462 =>
          cases assump_461
          case intro assump_463 assump_464 =>
            cases assump_463
            case inl assump_465 =>
              cases assump_465
              case intro assump_467 assump_468 =>
                cases assump_464
                case intro assump_473 assump_474 =>
                  cases assump_473
                  case inl assump_475 =>
                    cases assump_474
                    case inl assump_479 =>
                      have assump_699 : (p6 → p1) := by
                        intro assump_498
                        exact assump_479
                      let assump_497 := assump_3 assump_699
                      apply False.elim assump_497
                    case inr assump_480 =>
                      have assump_700 : (p6 → p1) := by
                        intro assump_521
                        exact assump_480
                      let assump_520 := assump_3 assump_700
                      apply False.elim assump_520
                  case inr assump_476 =>
                    cases assump_474
                    case inl assump_529 =>
                      have assump_701 : (p6 → p1) := by
                        intro assump_548
                        exact assump_529
                      let assump_547 := assump_3 assump_701
                      apply False.elim assump_547
                    case inr assump_530 =>
                      have assump_702 : (p6 → p1) := by
                        intro assump_571
                        exact assump_530
                      let assump_570 := assump_3 assump_702
                      apply False.elim assump_570
            case inr assump_466 =>
              cases assump_464
              case intro assump_579 assump_580 =>
                cases assump_579
                case inl assump_581 =>
                  cases assump_580
                  case inl assump_585 =>
                    have assump_703 : (p6 → p1) := by
                      intro assump_604
                      exact assump_585
                    let assump_603 := assump_3 assump_703
                    apply False.elim assump_603
                  case inr assump_586 =>
                    have assump_704 : (p6 → p1) := by
                      intro assump_627
                      exact assump_586
                    let assump_626 := assump_3 assump_704
                    apply False.elim assump_626
                case inr assump_582 =>
                  cases assump_580
                  case inl assump_635 =>
                    have assump_705 : (p6 → p1) := by
                      intro assump_654
                      exact assump_635
                    let assump_653 := assump_3 assump_705
                    apply False.elim assump_653
                  case inr assump_636 =>
                    have assump_706 : (p6 → p1) := by
                      intro assump_677
                      exact assump_636
                    let assump_676 := assump_3 assump_706
                    apply False.elim assump_676


variable (p3 p1 : Prop)
theorem file6_74986 : ((((((p3 ∨ True) → False) ∧ ((True ∧ p1) → False)) → False) → False) → False) := by
  intro assump_9
  have assump_28 : ((((p3 ∨ True) → False) ∧ ((True ∧ p1) → False)) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      have assump_29 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_21 := assump_14 assump_29
      apply False.elim assump_21
  let assump_12 := assump_9 assump_28
  apply False.elim assump_12


variable (p2 p7 p1 p5 p4 : Prop)
theorem file6_75535 : ((((((p2 → False) → (p4 ∨ p4)) ∧ ((p2 ∨ p1) → False)) ∧ (((False → False) → False) ∧ ((p4 → False) ∧ (p2 ∨ p7)))) ∧ ((((p4 ∨ p7) → (True → False)) → ((p1 ∨ p5) → (p7 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              have assump_78 : (((p4 ∨ p7) → (True → False)) → ((p1 ∨ p5) → (p7 → p2))) := by
                intro assump_27
                intro assump_28
                intro assump_29
                cases assump_28
                case inl assump_32 =>
                  exact assump_20
                case inr assump_33 =>
                  exact assump_20
              let assump_26 := assump_3 assump_78
              apply False.elim assump_26
            case inr assump_21 =>
              have assump_79 : (((p4 ∨ p7) → (True → False)) → ((p1 ∨ p5) → (p7 → p2))) := by
                intro assump_50
                intro assump_51
                intro assump_52
                cases assump_51
                case inl assump_55 =>
                  have assump_80 : (p4 ∨ p7) := by
                    apply Or.inr
                    exact assump_52
                  let assump_61 := assump_50 assump_80
                  have assump_81 : True := by
                    apply True.intro
                  let assump_62 := assump_61 assump_81
                  apply False.elim assump_62
                case inr assump_56 =>
                  have assump_82 : (p4 ∨ p7) := by
                    apply Or.inr
                    exact assump_52
                  let assump_70 := assump_50 assump_82
                  have assump_83 : True := by
                    apply True.intro
                  let assump_71 := assump_70 assump_83
                  apply False.elim assump_71
              let assump_49 := assump_3 assump_79
              apply False.elim assump_49


variable (p4 p3 p0 p6 p1 p7 p5 p2 : Prop)
theorem file6_77775 : (((((p2 → p4) → (p5 ∨ p1)) → False) → (((p5 ∧ p5) ∧ (True → False)) → ((p2 → False) ∧ (p1 → False)))) ∨ ((((p0 ∨ p0) ∨ (p2 ∨ False)) → False) → (((p3 ∧ p0) → (p0 → False)) ∨ ((p6 ∨ p4) ∨ (p7 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_47 : ((p2 → p4) → (p5 ∨ p1)) := by
        intro assump_19
        apply Or.inl
        exact assump_9
      let assump_18 := assump_1 assump_47
      apply False.elim assump_18
  intro assump_25
  cases assump_2
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      have assump_48 : ((p2 → p4) → (p5 ∨ p1)) := by
        intro assump_41
        apply Or.inl
        exact assump_31
      let assump_40 := assump_1 assump_48
      apply False.elim assump_40


variable (p2 p7 p3 p5 p4 p1 : Prop)
theorem file6_78754 : ((((((p4 ∧ p1) ∨ (p4 → False)) ∨ ((p2 ∧ p1) ∧ (p1 ∨ p7))) ∧ (((False ∧ p4) ∧ (p5 → p3)) ∨ ((p1 → p1) ∧ (p5 → p4)))) ∧ ((((False → False) ∨ (p2 ∧ p2)) ∨ ((p5 → False) → (p7 → False))) ∧ (((False → False) ∨ (p5 ∨ p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_5
            case inl assump_16 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  apply False.elim assump_20
            case inr assump_17 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                cases assump_3
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_32
                    case inl assump_34 =>
                      have assump_260 : ((False → False) ∨ (p5 ∨ p1)) := by
                        apply Or.inl
                        intro assump_41
                        apply False.elim assump_41
                      let assump_40 := assump_31 assump_260
                      apply False.elim assump_40
                    case inr assump_35 =>
                      cases assump_35
                      case intro assump_47 assump_48 =>
                        have assump_261 : ((False → False) ∨ (p5 ∨ p1)) := by
                          apply Or.inl
                          intro assump_56
                          apply False.elim assump_56
                        let assump_55 := assump_31 assump_261
                        apply False.elim assump_55
                  case inr assump_33 =>
                    have assump_262 : ((False → False) ∨ (p5 ∨ p1)) := by
                      apply Or.inl
                      intro assump_67
                      apply False.elim assump_67
                    let assump_66 := assump_31 assump_262
                    apply False.elim assump_66
        case inr assump_9 =>
          cases assump_5
          case inl assump_75 =>
            cases assump_75
            case intro assump_77 assump_78 =>
              cases assump_77
              case intro assump_79 assump_80 =>
                apply False.elim assump_79
          case inr assump_76 =>
            cases assump_76
            case intro assump_83 assump_84 =>
              cases assump_3
              case intro assump_89 assump_90 =>
                cases assump_89
                case inl assump_91 =>
                  cases assump_91
                  case inl assump_93 =>
                    have assump_263 : ((False → False) ∨ (p5 ∨ p1)) := by
                      apply Or.inl
                      intro assump_100
                      apply False.elim assump_100
                    let assump_99 := assump_90 assump_263
                    apply False.elim assump_99
                  case inr assump_94 =>
                    cases assump_94
                    case intro assump_106 assump_107 =>
                      have assump_264 : ((False → False) ∨ (p5 ∨ p1)) := by
                        apply Or.inl
                        intro assump_115
                        apply False.elim assump_115
                      let assump_114 := assump_90 assump_264
                      apply False.elim assump_114
                case inr assump_92 =>
                  have assump_265 : ((False → False) ∨ (p5 ∨ p1)) := by
                    apply Or.inl
                    intro assump_126
                    apply False.elim assump_126
                  let assump_125 := assump_90 assump_265
                  apply False.elim assump_125
      case inr assump_7 =>
        cases assump_7
        case intro assump_132 assump_133 =>
          cases assump_132
          case intro assump_134 assump_135 =>
            cases assump_133
            case inl assump_140 =>
              cases assump_5
              case inl assump_144 =>
                cases assump_144
                case intro assump_146 assump_147 =>
                  cases assump_146
                  case intro assump_148 assump_149 =>
                    apply False.elim assump_148
              case inr assump_145 =>
                cases assump_145
                case intro assump_152 assump_153 =>
                  cases assump_3
                  case intro assump_158 assump_159 =>
                    cases assump_158
                    case inl assump_160 =>
                      cases assump_160
                      case inl assump_162 =>
                        have assump_266 : ((False → False) ∨ (p5 ∨ p1)) := by
                          apply Or.inl
                          intro assump_169
                          apply False.elim assump_169
                        let assump_168 := assump_159 assump_266
                        apply False.elim assump_168
                      case inr assump_163 =>
                        cases assump_163
                        case intro assump_175 assump_176 =>
                          have assump_267 : ((False → False) ∨ (p5 ∨ p1)) := by
                            apply Or.inl
                            intro assump_184
                            apply False.elim assump_184
                          let assump_183 := assump_159 assump_267
                          apply False.elim assump_183
                    case inr assump_161 =>
                      have assump_268 : ((False → False) ∨ (p5 ∨ p1)) := by
                        apply Or.inl
                        intro assump_195
                        apply False.elim assump_195
                      let assump_194 := assump_159 assump_268
                      apply False.elim assump_194
            case inr assump_141 =>
              cases assump_5
              case inl assump_203 =>
                cases assump_203
                case intro assump_205 assump_206 =>
                  cases assump_205
                  case intro assump_207 assump_208 =>
                    apply False.elim assump_207
              case inr assump_204 =>
                cases assump_204
                case intro assump_211 assump_212 =>
                  cases assump_3
                  case intro assump_217 assump_218 =>
                    cases assump_217
                    case inl assump_219 =>
                      cases assump_219
                      case inl assump_221 =>
                        have assump_269 : ((False → False) ∨ (p5 ∨ p1)) := by
                          apply Or.inl
                          intro assump_228
                          apply False.elim assump_228
                        let assump_227 := assump_218 assump_269
                        apply False.elim assump_227
                      case inr assump_222 =>
                        cases assump_222
                        case intro assump_234 assump_235 =>
                          have assump_270 : ((False → False) ∨ (p5 ∨ p1)) := by
                            apply Or.inl
                            intro assump_243
                            apply False.elim assump_243
                          let assump_242 := assump_218 assump_270
                          apply False.elim assump_242
                    case inr assump_220 =>
                      have assump_271 : ((False → False) ∨ (p5 ∨ p1)) := by
                        apply Or.inl
                        intro assump_254
                        apply False.elim assump_254
                      let assump_253 := assump_218 assump_271
                      apply False.elim assump_253


variable (p0 p1 p7 p2 p5 p4 p6 : Prop)
theorem file6_86714 : (((((False ∧ p5) ∧ (p0 ∧ p7)) → False) → (((p1 → p2) ∨ (False → p6)) ∨ ((p1 ∨ p6) ∧ (p6 ∨ p7)))) → ((((p0 ∨ p6) → (True ∧ p4)) ∨ ((p4 ∨ True) ∧ (False → p5))) → (((True ∧ False) ∧ (p7 ∧ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p1 p3 p6 p7 p2 p0 p5 : Prop)
theorem file6_87174 : (((((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) → False) → ((((p1 ∧ p1) ∨ (p3 ∨ p0)) → ((p5 → False) → False)) ∧ (((p6 ∧ p2) ∨ (p2 ∨ p3)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_101 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_17
        intro assump_18
        intro assump_19
        apply False.elim assump_19
      let assump_16 := assump_1 assump_101
      apply False.elim assump_16
  case inr assump_7 =>
    cases assump_7
    case inl assump_25 =>
      have assump_102 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_32
        intro assump_33
        intro assump_34
        apply False.elim assump_34
      let assump_31 := assump_1 assump_102
      apply False.elim assump_31
    case inr assump_26 =>
      have assump_103 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_45
        intro assump_46
        intro assump_47
        apply False.elim assump_47
      let assump_44 := assump_1 assump_103
      apply False.elim assump_44
  intro assump_53
  cases assump_53
  case inl assump_54 =>
    cases assump_54
    case intro assump_56 assump_57 =>
      have assump_104 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_65
        intro assump_66
        intro assump_67
        apply False.elim assump_67
      let assump_64 := assump_1 assump_104
      apply False.elim assump_64
  case inr assump_55 =>
    cases assump_55
    case inl assump_73 =>
      have assump_105 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_80
        intro assump_81
        intro assump_82
        apply False.elim assump_82
      let assump_79 := assump_1 assump_105
      apply False.elim assump_79
    case inr assump_74 =>
      have assump_106 : (((p1 ∧ p0) → False) → ((p7 ∨ p3) → (False → False))) := by
        intro assump_93
        intro assump_94
        intro assump_95
        apply False.elim assump_95
      let assump_92 := assump_1 assump_106
      apply False.elim assump_92


variable (p4 p2 p0 : Prop)
theorem file6_89462 : (((((True ∨ p4) → False) → ((p4 ∧ p2) ∧ (p4 → p0))) → False) → False) := by
  intro assump_1
  have assump_30 : (((True ∨ p4) → False) → ((p4 ∧ p2) ∧ (p4 → p0))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    have assump_31 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_31
    apply False.elim assump_8
    have assump_32 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_14 := assump_5 assump_32
    apply False.elim assump_14
    intro assump_18
    have assump_33 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_23 := assump_5 assump_33
    apply False.elim assump_23
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p1 p6 p0 : Prop)
theorem file6_90282 : (((((p2 ∧ p0) → (False → True)) ∧ ((p6 → p1) → (p2 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p2 ∧ p0) → (False → True)) ∧ ((p6 → p1) → (p2 ∨ True))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply True.intro
    intro assump_7
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p0 p4 p6 p1 : Prop)
theorem file6_90726 : ((((((True → False) → False) ∧ ((p0 ∧ False) → False)) → (((False → p1) ∨ (p4 ∨ p0)) ∨ ((p1 → False) ∨ (p1 → p6)))) ∧ ((((False ∧ p1) ∧ (p6 → False)) → ((p6 → False) → (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((False ∧ p1) ∧ (p6 → False)) → ((p6 → False) → (p3 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_9
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p3 p6 p5 p2 p4 p0 p7 : Prop)
theorem file6_91454 : (((((True ∨ p5) → (p3 → p7)) ∧ ((True ∧ True) → False)) ∧ (((True → False) ∧ (p4 ∨ p2)) ∨ ((p5 → p4) ∨ (True → False)))) → ((((p7 ∨ p4) → (p3 ∨ p6)) → False) ∧ (((p3 ∨ p0) → False) ∧ ((p3 ∨ p2) ∨ (p0 ∨ p3))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            have assump_187 : True := by
              apply True.intro
            let assump_24 := assump_15 assump_187
            apply False.elim assump_24
          case inr assump_20 =>
            have assump_188 : True := by
              apply True.intro
            let assump_31 := assump_15 assump_188
            apply False.elim assump_31
      case inr assump_14 =>
        cases assump_14
        case inl assump_35 =>
          have assump_189 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_40 := assump_8 assump_189
          apply False.elim assump_40
        case inr assump_36 =>
          have assump_190 : True := by
            apply True.intro
          let assump_46 := assump_36 assump_190
          apply False.elim assump_46
  apply And.intro
  intro assump_50
  cases assump_50
  case inl assump_51 =>
    cases assump_1
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        cases assump_56
        case inl assump_63 =>
          cases assump_63
          case intro assump_65 assump_66 =>
            cases assump_66
            case inl assump_69 =>
              have assump_191 : True := by
                apply True.intro
              let assump_74 := assump_65 assump_191
              apply False.elim assump_74
            case inr assump_70 =>
              have assump_192 : True := by
                apply True.intro
              let assump_81 := assump_65 assump_192
              apply False.elim assump_81
        case inr assump_64 =>
          cases assump_64
          case inl assump_85 =>
            have assump_193 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_90 := assump_58 assump_193
            apply False.elim assump_90
          case inr assump_86 =>
            have assump_194 : True := by
              apply True.intro
            let assump_96 := assump_86 assump_194
            apply False.elim assump_96
  case inr assump_52 =>
    cases assump_1
    case intro assump_102 assump_103 =>
      cases assump_102
      case intro assump_104 assump_105 =>
        cases assump_103
        case inl assump_110 =>
          cases assump_110
          case intro assump_112 assump_113 =>
            cases assump_113
            case inl assump_116 =>
              have assump_195 : True := by
                apply True.intro
              let assump_121 := assump_112 assump_195
              apply False.elim assump_121
            case inr assump_117 =>
              have assump_196 : True := by
                apply True.intro
              let assump_128 := assump_112 assump_196
              apply False.elim assump_128
        case inr assump_111 =>
          cases assump_111
          case inl assump_132 =>
            have assump_197 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_137 := assump_105 assump_197
            apply False.elim assump_137
          case inr assump_133 =>
            have assump_198 : True := by
              apply True.intro
            let assump_143 := assump_133 assump_198
            apply False.elim assump_143
  cases assump_1
  case intro assump_147 assump_148 =>
    cases assump_147
    case intro assump_149 assump_150 =>
      cases assump_148
      case inl assump_155 =>
        cases assump_155
        case intro assump_157 assump_158 =>
          cases assump_158
          case inl assump_161 =>
            have assump_199 : True := by
              apply True.intro
            let assump_166 := assump_157 assump_199
            apply False.elim assump_166
          case inr assump_162 =>
            apply Or.inl
            apply Or.inr
            exact assump_162
      case inr assump_156 =>
        cases assump_156
        case inl assump_172 =>
          have assump_200 : (True ∧ True) := by
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_177 := assump_150 assump_200
          apply False.elim assump_177
        case inr assump_173 =>
          have assump_201 : True := by
            apply True.intro
          let assump_183 := assump_173 assump_201
          apply False.elim assump_183


variable (p1 p2 p7 p0 : Prop)
theorem file6_96468 : (((((p2 → False) → (p1 → True)) ∨ ((False → False) ∨ (p0 → p7))) → False) → False) := by
  intro assump_41
  have assump_50 : (((p2 → False) → (p1 → True)) ∨ ((False → False) ∨ (p0 → p7))) := by
    apply Or.inl
    intro assump_45
    intro assump_46
    apply True.intro
  let assump_44 := assump_41 assump_50
  apply False.elim assump_44


variable (p6 p0 p2 p5 p7 p3 : Prop)
theorem file6_96869 : (((((p2 → p2) → False) → ((p0 ∨ True) ∧ (p0 ∧ p0))) ∨ (((True ∧ p5) → (p6 → True)) ∧ ((False ∧ p5) → (True ∧ p7)))) ∨ ((((True ∧ p7) ∨ (p5 → False)) ∧ ((p5 → p5) → False)) ∧ (((p7 ∧ False) → False) ∨ ((p3 ∨ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inr
  apply True.intro
  apply And.intro
  have assump_22 : (p2 → p2) := by
    intro assump_7
    exact assump_7
  let assump_6 := assump_1 assump_22
  apply False.elim assump_6
  have assump_23 : (p2 → p2) := by
    intro assump_16
    exact assump_16
  let assump_15 := assump_1 assump_23
  apply False.elim assump_15


variable (p4 p3 p1 p0 p2 : Prop)
theorem file6_97552 : ((((((p0 → False) ∨ (p2 → p3)) → False) → (((True ∨ True) → False) → False)) ∧ ((((False ∧ False) ∨ (False ∧ p1)) ∨ ((p4 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False ∧ False) ∨ (False ∧ p1)) ∨ ((p4 ∧ False) → False)) := by
      apply Or.inr
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p2 p5 p3 p4 : Prop)
theorem file6_98131 : (((((False → p2) → False) → False) → False) → ((((p5 ∧ p4) ∧ (p4 → p4)) ∧ ((p4 → False) ∨ (p3 ∨ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_15 =>
          have assump_73 : (((False → p2) → False) → False) := by
            intro assump_22
            have assump_74 : (False → p2) := by
              intro assump_26
              apply False.elim assump_26
            let assump_25 := assump_22 assump_74
            apply False.elim assump_25
          let assump_21 := assump_1 assump_73
          apply False.elim assump_21
        case inr assump_16 =>
          cases assump_16
          case inl assump_35 =>
            have assump_75 : (((False → p2) → False) → False) := by
              intro assump_42
              have assump_76 : (False → p2) := by
                intro assump_46
                apply False.elim assump_46
              let assump_45 := assump_42 assump_76
              apply False.elim assump_45
            let assump_41 := assump_1 assump_75
            apply False.elim assump_41
          case inr assump_36 =>
            have assump_77 : (((False → p2) → False) → False) := by
              intro assump_60
              have assump_78 : (False → p2) := by
                intro assump_64
                apply False.elim assump_64
              let assump_63 := assump_60 assump_78
              apply False.elim assump_63
            let assump_59 := assump_1 assump_77
            apply False.elim assump_59


variable (p3 p5 p7 p0 p4 : Prop)
theorem file6_99866 : ((((((p4 ∧ True) → (True → p7)) ∨ ((p4 ∧ p4) ∧ (p5 → False))) → (((p4 → p3) ∧ (True → p4)) → ((p0 → True) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 ∧ True) → (True → p7)) ∨ ((p4 ∧ p4) ∧ (p5 → False))) → (((p4 → p3) ∧ (True → p4)) → ((p0 → True) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p7 p5 p6 p4 p1 p0 : Prop)
theorem file6_100418 : ((((((p0 → p7) → (p4 ∧ p5)) → ((p1 → False) ∨ (p0 ∧ p1))) ∨ (((p7 → False) → False) ∨ ((p3 → False) → False))) ∧ ((((p6 → False) ∨ (False ∧ p6)) → ((False → False) ∨ (True → False))) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      have assump_77 : (((p6 → False) ∨ (False ∧ p6)) → ((False → False) ∨ (True → False))) := by
        intro assump_20
        cases assump_20
        case inl assump_21 =>
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
        case inr assump_22 =>
          cases assump_22
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
      let assump_19 := assump_12 assump_77
      apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case inl assump_35 =>
        have assump_78 : (((p6 → False) ∨ (False ∧ p6)) → ((False → False) ∨ (True → False))) := by
          intro assump_42
          cases assump_42
          case inl assump_43 =>
            apply Or.inl
            intro assump_47
            apply False.elim assump_47
          case inr assump_44 =>
            cases assump_44
            case intro assump_50 assump_51 =>
              apply False.elim assump_50
        let assump_41 := assump_12 assump_78
        apply False.elim assump_41
      case inr assump_36 =>
        have assump_79 : (((p6 → False) ∨ (False ∧ p6)) → ((False → False) ∨ (True → False))) := by
          intro assump_62
          cases assump_62
          case inl assump_63 =>
            apply Or.inl
            intro assump_67
            apply False.elim assump_67
          case inr assump_64 =>
            cases assump_64
            case intro assump_70 assump_71 =>
              apply False.elim assump_70
        let assump_61 := assump_12 assump_79
        apply False.elim assump_61


variable (p6 p3 p0 p1 p7 : Prop)
theorem file6_102388 : (((((p7 → False) → False) ∧ ((True → p1) → (p6 → False))) → False) → ((((False ∧ p3) ∧ (True ∨ True)) ∨ ((p0 → False) ∧ (False ∧ p7))) → (((p1 → False) → (p1 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  case inr assump_7 =>
    cases assump_7
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply False.elim assump_18


variable (p4 p1 p5 p0 p3 p2 p7 : Prop)
theorem file6_103055 : (((((p4 → p5) ∨ (p0 → False)) ∧ ((p0 → False) ∧ (p0 ∧ False))) → (((p2 ∨ p5) ∨ (p5 → False)) ∧ ((p4 → False) ∧ (True → False)))) ∨ ((((p2 ∨ p2) ∨ (p1 → p0)) ∧ ((True ∧ False) ∧ (p3 ∧ p4))) ∨ (((p3 → False) → (p7 → False)) → ((False ∧ p5) ∧ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    case inr assump_5 =>
      cases assump_3
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          apply False.elim assump_25
  apply And.intro
  intro assump_30
  cases assump_1
  case intro assump_33 assump_34 =>
    cases assump_33
    case inl assump_35 =>
      cases assump_34
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          apply False.elim assump_44
    case inr assump_36 =>
      cases assump_34
      case intro assump_51 assump_52 =>
        cases assump_52
        case intro assump_55 assump_56 =>
          apply False.elim assump_56
  intro assump_61
  cases assump_1
  case intro assump_64 assump_65 =>
    cases assump_64
    case inl assump_66 =>
      cases assump_65
      case intro assump_70 assump_71 =>
        cases assump_71
        case intro assump_74 assump_75 =>
          apply False.elim assump_75
    case inr assump_67 =>
      cases assump_65
      case intro assump_82 assump_83 =>
        cases assump_83
        case intro assump_86 assump_87 =>
          apply False.elim assump_87


variable (p2 p1 p3 p7 p0 p5 : Prop)
theorem file6_104837 : (((((p3 → False) ∧ (p7 → False)) ∧ ((True ∨ p0) → False)) ∧ (((p5 ∧ p2) → (False ∧ p7)) ∨ ((p3 ∧ p1) → False))) → ((((True ∨ p1) → (True → False)) → False) ∧ (((p5 → p0) → False) ∧ ((p7 ∨ True) → (False ∧ False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case inl assump_17 =>
          have assump_189 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_22 := assump_8 assump_189
          apply False.elim assump_22
        case inr assump_18 =>
          have assump_190 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_29 := assump_8 assump_190
          apply False.elim assump_29
  apply And.intro
  intro assump_33
  cases assump_1
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_37
        case inl assump_48 =>
          have assump_191 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_53 := assump_39 assump_191
          apply False.elim assump_53
        case inr assump_49 =>
          have assump_192 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_60 := assump_39 assump_192
          apply False.elim assump_60
  intro assump_64
  apply And.intro
  cases assump_64
  case inl assump_65 =>
    cases assump_1
    case intro assump_69 assump_70 =>
      cases assump_69
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_70
          case inl assump_81 =>
            have assump_193 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_86 := assump_72 assump_193
            apply False.elim assump_86
          case inr assump_82 =>
            have assump_194 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_93 := assump_72 assump_194
            apply False.elim assump_93
  case inr assump_66 =>
    cases assump_1
    case intro assump_99 assump_100 =>
      cases assump_99
      case intro assump_101 assump_102 =>
        cases assump_101
        case intro assump_103 assump_104 =>
          cases assump_100
          case inl assump_111 =>
            have assump_195 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_116 := assump_102 assump_195
            apply False.elim assump_116
          case inr assump_112 =>
            have assump_196 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_123 := assump_102 assump_196
            apply False.elim assump_123
  cases assump_64
  case inl assump_127 =>
    cases assump_1
    case intro assump_131 assump_132 =>
      cases assump_131
      case intro assump_133 assump_134 =>
        cases assump_133
        case intro assump_135 assump_136 =>
          cases assump_132
          case inl assump_143 =>
            have assump_197 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_148 := assump_134 assump_197
            apply False.elim assump_148
          case inr assump_144 =>
            have assump_198 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_155 := assump_134 assump_198
            apply False.elim assump_155
  case inr assump_128 =>
    cases assump_1
    case intro assump_161 assump_162 =>
      cases assump_161
      case intro assump_163 assump_164 =>
        cases assump_163
        case intro assump_165 assump_166 =>
          cases assump_162
          case inl assump_173 =>
            have assump_199 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_178 := assump_164 assump_199
            apply False.elim assump_178
          case inr assump_174 =>
            have assump_200 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_185 := assump_164 assump_200
            apply False.elim assump_185


variable (p3 p2 p4 p5 p1 p7 : Prop)
theorem file6_109330 : (((((p2 ∨ True) ∧ (p1 ∨ p2)) ∨ ((False → False) → (p5 ∨ p4))) → False) → ((((p5 → False) ∨ (p7 ∨ p3)) ∨ ((p4 → False) ∨ (p5 ∧ p7))) ∨ (((p4 → False) ∧ (p2 → p4)) ∨ ((p2 ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_15 : (((p2 ∨ True) ∧ (p1 ∨ p2)) ∨ ((False → False) → (p5 ∨ p4))) := by
    apply Or.inr
    intro assump_9
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p3 p5 p6 p0 p2 : Prop)
theorem file6_109881 : ((((((p5 → False) ∧ (p6 ∧ False)) → ((p2 ∧ True) → False)) → (((p2 ∨ p3) → False) ∨ ((p2 ∨ p5) ∧ (p6 ∨ False)))) ∧ ((((p0 ∧ True) ∨ (p0 → False)) ∧ ((True ∨ p2) ∨ (True → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p0 ∧ True) ∨ (p0 → False)) ∧ ((True ∨ p2) ∨ (True → False))) := by
      apply And.intro
      apply Or.inr
      intro assump_9
      have assump_21 : (((p0 ∧ True) ∨ (p0 → False)) ∧ ((True ∨ p2) ∨ (True → False))) := by
        apply And.intro
        apply Or.inl
        apply And.intro
        exact assump_9
        apply True.intro
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p4 p5 p1 p2 p7 p6 p0 p3 : Prop)
theorem file6_110855 : (((((p3 → p5) ∨ (p3 ∨ p0)) ∧ ((p4 ∧ p6) ∧ (p4 → False))) → (((p6 → False) ∨ (p5 → p3)) ∧ ((p6 → False) → False))) ∨ ((((p5 → p2) ∧ (p2 ∨ p1)) → False) ∨ (((False → p6) ∨ (p0 → p4)) ∨ ((p4 ∨ p6) ∨ (p7 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_18
          have assump_125 : p4 := by
            exact assump_10
          let assump_22 := assump_9 assump_125
          apply False.elim assump_22
    case inr assump_5 =>
      cases assump_5
      case inl assump_26 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply Or.inl
            intro assump_40
            have assump_126 : p4 := by
              exact assump_32
            let assump_44 := assump_31 assump_126
            apply False.elim assump_44
      case inr assump_27 =>
        cases assump_3
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            apply Or.inl
            intro assump_60
            have assump_127 : p4 := by
              exact assump_52
            let assump_64 := assump_51 assump_127
            apply False.elim assump_64
  intro assump_68
  cases assump_1
  case intro assump_71 assump_72 =>
    cases assump_71
    case inl assump_73 =>
      cases assump_72
      case intro assump_77 assump_78 =>
        cases assump_77
        case intro assump_79 assump_80 =>
          have assump_128 : p4 := by
            exact assump_79
          let assump_87 := assump_78 assump_128
          apply False.elim assump_87
    case inr assump_74 =>
      cases assump_74
      case inl assump_91 =>
        cases assump_72
        case intro assump_95 assump_96 =>
          cases assump_95
          case intro assump_97 assump_98 =>
            have assump_129 : p4 := by
              exact assump_97
            let assump_105 := assump_96 assump_129
            apply False.elim assump_105
      case inr assump_92 =>
        cases assump_72
        case intro assump_111 assump_112 =>
          cases assump_111
          case intro assump_113 assump_114 =>
            have assump_130 : p4 := by
              exact assump_113
            let assump_121 := assump_112 assump_130
            apply False.elim assump_121


variable (p6 p3 p7 p5 p0 p4 : Prop)
theorem file6_113490 : (((((p6 ∨ True) → False) → ((True ∧ False) → False)) ∨ (((p6 ∧ p3) ∨ (False ∨ p7)) → ((False → p4) ∨ (p6 ∧ p3)))) ∨ ((((p3 ∧ True) ∨ (p0 ∧ p7)) ∧ ((p5 → False) ∧ (p4 ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p7 p6 p1 : Prop)
theorem file6_113876 : ((((((False ∨ False) → False) → False) → (((p6 ∨ False) ∨ (p1 → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_46 : ((((False ∨ False) → False) → False) → (((p6 ∨ False) ∨ (p1 → p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_47 : ((False ∨ False) → False) := by
          intro assump_16
          cases assump_16
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply False.elim assump_18
        let assump_15 := assump_5 assump_47
        apply False.elim assump_15
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      have assump_48 : ((False ∨ False) → False) := by
        intro assump_33
        cases assump_33
        case inl assump_34 =>
          apply False.elim assump_34
        case inr assump_35 =>
          apply False.elim assump_35
      let assump_32 := assump_5 assump_48
      apply False.elim assump_32
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p3 p5 p6 p4 p1 : Prop)
theorem file6_115080 : ((((((p3 ∨ p1) → (p4 → p1)) → False) → (((True ∨ p5) ∨ (p5 → p5)) ∨ ((p6 → False) → False))) → False) → False) := by
  intro assump_5
  have assump_15 : ((((p3 ∨ p1) → (p4 → p1)) → False) → (((True ∨ p5) ∨ (p5 → p5)) ∨ ((p6 → False) → False))) := by
    intro assump_9
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p3 p2 p1 p7 p4 p5 p6 : Prop)
theorem file6_115549 : (((((False → p1) ∨ (p1 ∨ p4)) → False) → (((False ∧ False) ∧ (p1 ∨ p5)) → False)) ∨ ((((p3 ∧ p2) → (p6 ∧ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p4 p3 p2 p0 p1 p5 p6 p7 : Prop)
theorem file6_115937 : ((((((p0 ∧ p7) ∨ (True → False)) → ((p0 → p4) ∧ (p1 → True))) ∧ (((p2 ∨ p5) → False) → ((p4 ∨ True) ∨ (p1 ∨ p5)))) ∧ ((((False ∨ True) ∨ (True ∨ p4)) → False) ∧ (((p5 → False) ∨ (p4 → True)) ∨ ((p3 ∨ p6) → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            have assump_43 : ((False ∨ True) ∨ (True ∨ p4)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_25 := assump_14 assump_43
            apply False.elim assump_25
          case inr assump_21 =>
            have assump_44 : ((False ∨ True) ∨ (True ∨ p4)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_32 := assump_14 assump_44
            apply False.elim assump_32
        case inr assump_19 =>
          have assump_45 : ((False ∨ True) ∨ (True ∨ p4)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_39 := assump_14 assump_45
          apply False.elim assump_39


variable (p4 p0 p3 p1 p5 p6 : Prop)
theorem file6_117291 : ((((((p4 → p4) ∧ (p0 → False)) ∧ ((p4 → False) → (p5 ∧ p6))) → False) ∧ ((((p6 ∨ p0) ∧ (False ∧ p0)) ∧ ((p5 ∧ p1) ∧ (True ∧ p3))) ∧ (((p5 → p4) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_13 =>
            cases assump_11
            case intro assump_22 assump_23 =>
              apply False.elim assump_22


variable (p4 p2 p3 p7 p0 p5 p1 : Prop)
theorem file6_118100 : (((((p5 → p2) ∨ (p7 ∧ p0)) → ((p4 → p3) ∧ (p1 ∨ False))) ∧ (((p2 → False) → (True ∨ p5)) → False)) → False) := by
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    have assump_42 : ((p2 → False) → (True ∨ p5)) := by
      intro assump_36
      apply Or.inl
      apply True.intro
    let assump_35 := assump_30 assump_42
    apply False.elim assump_35


variable (p4 p6 p0 p5 p3 p1 p7 p2 : Prop)
theorem file6_118544 : (((((False → False) → False) → False) → False) → ((((p7 → False) → (False ∨ p5)) → ((p0 ∧ p5) ∧ (p4 ∧ p3))) → (((p1 ∧ True) ∧ (p2 → False)) → ((p6 → False) ∧ (p2 → False))))) := by
  intro assump_8
  intro assump_9
  intro assump_10
  apply And.intro
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      have assump_73 : (((False → False) → False) → False) := by
        intro assump_29
        have assump_74 : (False → False) := by
          intro assump_33
          apply False.elim assump_33
        let assump_32 := assump_29 assump_74
        apply False.elim assump_32
      let assump_28 := assump_8 assump_73
      apply False.elim assump_28
  intro assump_42
  cases assump_10
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      have assump_75 : (((False → False) → False) → False) := by
        intro assump_60
        have assump_76 : (False → False) := by
          intro assump_64
          apply False.elim assump_64
        let assump_63 := assump_60 assump_76
        apply False.elim assump_63
      let assump_59 := assump_8 assump_75
      apply False.elim assump_59


variable (p5 p3 p7 p4 p6 p0 p2 : Prop)
theorem file6_119826 : ((((((p7 ∧ False) ∧ (p6 → False)) ∧ ((False → False) → False)) ∧ (((p6 → True) → (p2 ∧ p2)) ∧ ((p0 ∧ p3) ∨ (p2 → p5)))) ∧ ((((p2 ∧ p7) ∧ (False ∨ False)) → ((p4 → p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_11


variable (p0 p5 p1 p6 p3 : Prop)
theorem file6_120438 : ((((((p0 ∨ p1) ∧ (p5 ∨ False)) ∨ ((p6 ∧ p3) → False)) → (((True ∧ True) → False) → ((p1 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p0 ∨ p1) ∧ (p5 ∨ False)) ∨ ((p6 ∧ p3) → False)) → (((True ∧ True) → False) → ((p1 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case inl assump_20 =>
            have assump_57 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_26 := assump_6 assump_57
            apply False.elim assump_26
          case inr assump_21 =>
            apply False.elim assump_21
        case inr assump_17 =>
          cases assump_15
          case inl assump_34 =>
            have assump_58 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_40 := assump_6 assump_58
            apply False.elim assump_40
          case inr assump_35 =>
            apply False.elim assump_35
    case inr assump_13 =>
      have assump_59 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_49 := assump_6 assump_59
      apply False.elim assump_49
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p1 p4 p0 p7 : Prop)
theorem file6_122017 : (((((p7 ∨ p1) ∨ (True ∨ p7)) ∨ ((p4 → False) → (p0 ∧ p1))) → False) → False) := by
  intro assump_9
  have assump_16 : (((p7 ∨ p1) ∨ (True ∨ p7)) ∨ ((p4 → False) → (p0 ∧ p1))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_12 := assump_9 assump_16
  apply False.elim assump_12


variable (p4 p6 p7 p2 p3 p0 p1 p5 : Prop)
theorem file6_122404 : (((((p3 → False) ∧ (False ∨ p5)) → ((False ∨ p7) → (p5 → p7))) ∨ (((p7 ∧ p4) → False) ∧ ((p2 → False) → False))) ∨ ((((p7 → False) ∧ (p0 ∧ p5)) → False) ∨ (((p5 → p6) ∨ (p1 → False)) → ((p0 ∧ p2) → (p0 → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply False.elim assump_6
  case inr assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        apply False.elim assump_16
      case inr assump_17 =>
        exact assump_7


variable (p5 p4 p7 p0 p1 p2 p3 : Prop)
theorem file6_123052 : ((((((p4 ∨ p2) ∧ (p4 → False)) ∨ ((p4 → False) ∨ (p5 ∨ p3))) ∧ (((False ∧ p3) ∧ (False → p0)) ∧ ((p5 ∨ p7) → (p4 ∨ p1)))) ∧ ((((p2 → p7) ∨ (False → False)) → ((p7 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  apply False.elim assump_20
          case inr assump_11 =>
            cases assump_5
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
      case inr assump_7 =>
        cases assump_7
        case inl assump_36 =>
          cases assump_5
          case intro assump_40 assump_41 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                apply False.elim assump_44
        case inr assump_37 =>
          cases assump_37
          case inl assump_48 =>
            cases assump_5
            case intro assump_52 assump_53 =>
              cases assump_52
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  apply False.elim assump_56
          case inr assump_49 =>
            cases assump_5
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  apply False.elim assump_66


variable (p5 p2 p3 p6 p1 p7 : Prop)
theorem file6_125218 : ((((((True → False) → (p7 ∨ p5)) → False) → (((True ∨ p2) → (p7 → p3)) ∧ ((False ∨ p6) → (p1 → p2)))) → False) → False) := by
  intro assump_5
  have assump_64 : ((((True → False) → (p7 ∨ p5)) → False) → (((True ∨ p2) → (p7 → p3)) ∧ ((False ∨ p6) → (p1 → p2)))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    intro assump_11
    cases assump_10
    case inl assump_14 =>
      have assump_65 : ((True → False) → (p7 ∨ p5)) := by
        intro assump_21
        apply Or.inl
        exact assump_11
      let assump_20 := assump_9 assump_65
      apply False.elim assump_20
    case inr assump_15 =>
      have assump_66 : ((True → False) → (p7 ∨ p5)) := by
        intro assump_32
        apply Or.inl
        exact assump_11
      let assump_31 := assump_9 assump_66
      apply False.elim assump_31
    intro assump_38
    intro assump_39
    cases assump_38
    case inl assump_42 =>
      apply False.elim assump_42
    case inr assump_43 =>
      have assump_67 : ((True → False) → (p7 ∨ p5)) := by
        intro assump_51
        have assump_68 : True := by
          apply True.intro
        let assump_54 := assump_51 assump_68
        apply False.elim assump_54
      let assump_50 := assump_9 assump_67
      apply False.elim assump_50
  let assump_8 := assump_5 assump_64
  apply False.elim assump_8


variable (p0 p4 p6 p1 p7 p2 : Prop)
theorem file6_126611 : (((((False → False) ∨ (p2 → False)) → False) → False) ∨ ((((p7 → False) → (p6 ∧ p2)) → ((p4 → p6) ∨ (p0 ∧ p1))) → (((True → False) ∧ (p2 → p4)) → ((p2 → p6) ∧ (p1 ∨ False))))) := by
  apply Or.inl
  intro assump_5
  have assump_15 : ((False → False) ∨ (p2 → False)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p0 p7 p5 p6 p2 p4 p1 : Prop)
theorem file6_127077 : (((((p0 → False) ∧ (False ∧ p0)) → ((p2 ∧ True) ∨ (p5 → p4))) ∨ (((p0 ∧ p4) ∧ (p1 ∧ p2)) ∨ ((p2 → False) → (p1 → False)))) ∨ ((((p7 ∧ p1) ∨ (p5 → False)) → ((p2 → False) ∧ (p2 ∨ p7))) → (((p6 ∧ p4) → (p4 ∧ p5)) ∧ ((p4 ∨ True) → (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_28
    case intro assump_31 assump_32 =>
      apply False.elim assump_31


variable (p5 p4 p2 p1 p6 : Prop)
theorem file6_127578 : (((((True ∨ p5) → (False ∧ p2)) → False) ∧ (((p6 ∨ p4) → (p1 → p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : ((p6 ∨ p4) → (p1 → p1)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case inl assump_13 =>
        exact assump_10
      case inr assump_14 =>
        exact assump_10
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p1 p4 p2 p6 p3 p7 : Prop)
theorem file6_128087 : (((((True → False) → False) → False) → (((p2 ∨ p7) ∧ (p6 ∨ p1)) ∨ ((p3 → False) → (p2 → p3)))) ∨ ((((p4 → False) ∧ (p7 → p3)) ∧ ((p7 → False) → (True ∨ p7))) ∨ (((p2 ∧ p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  have assump_23 : ((True → False) → False) := by
    intro assump_13
    have assump_24 : True := by
      apply True.intro
    let assump_16 := assump_13 assump_24
    apply False.elim assump_16
  let assump_12 := assump_1 assump_23
  apply False.elim assump_12


variable (p1 p3 p7 p5 p6 p4 : Prop)
theorem file6_128690 : ((((((p3 ∧ p3) ∧ (p4 ∧ p7)) ∧ ((p1 ∨ True) → (p7 → False))) ∧ (((p1 → True) → False) ∧ ((True → p7) → (p1 ∧ p3)))) ∨ ((((p4 → p4) → (p5 ∧ p6)) → ((p4 → False) → (False → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_5
              case intro assump_24 assump_25 =>
                have assump_53 : (p1 → True) := by
                  intro assump_38
                  apply True.intro
                let assump_37 := assump_24 assump_53
                apply False.elim assump_37
  case inr assump_3 =>
    have assump_54 : (((p4 → p4) → (p5 ∧ p6)) → ((p4 → False) → (False → p3))) := by
      intro assump_45
      intro assump_46
      intro assump_47
      apply False.elim assump_47
    let assump_44 := assump_3 assump_54
    apply False.elim assump_44


variable (p2 p5 p3 p4 p7 p0 p1 : Prop)
theorem file6_129901 : ((((((p7 ∨ p0) ∧ (p3 ∨ p1)) → ((p1 ∨ p4) ∨ (p2 → False))) → (((p0 ∨ p2) ∧ (p2 → p2)) ∨ ((False → False) ∨ (p5 → p2)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p7 ∨ p0) ∧ (p3 ∨ p1)) → ((p1 ∨ p4) ∨ (p2 → False))) → (((p0 ∨ p2) ∧ (p2 → p2)) ∨ ((False → False) ∨ (p5 → p2)))) := by
    intro assump_5
    apply Or.inr
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p4 p1 p3 p7 p0 p6 : Prop)
theorem file6_130433 : (((((False → p0) ∧ (p6 ∨ True)) → False) → (((p4 → False) → False) → ((p2 → False) ∨ (False → p3)))) ∨ ((((p0 ∧ p1) → (p7 ∧ False)) → ((True → False) ∧ (p2 → p7))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_18 : ((False → p0) ∧ (p6 ∨ True)) := by
    apply And.intro
    intro assump_12
    apply False.elim assump_12
    apply Or.inr
    apply True.intro
  let assump_11 := assump_1 assump_18
  apply False.elim assump_11


variable (p7 p4 p6 p2 p0 : Prop)
theorem file6_130981 : ((((((p0 → False) → False) ∧ ((False → p0) → False)) → (((p7 ∨ p6) → (p6 ∨ p6)) → ((p0 → p4) ∨ (p2 ∨ p2)))) → False) → False) := by
  intro assump_7
  have assump_35 : ((((p0 → False) → False) ∧ ((False → p0) → False)) → (((p7 ∨ p6) → (p6 ∨ p6)) → ((p0 → p4) ∨ (p2 ∨ p2)))) := by
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_21
      have assump_36 : (False → p0) := by
        intro assump_26
        apply False.elim assump_26
      let assump_25 := assump_16 assump_36
      apply False.elim assump_25
  let assump_10 := assump_7 assump_35
  apply False.elim assump_10


variable (p4 p1 p7 p2 p3 p0 : Prop)
theorem file6_131704 : ((((((True ∨ p7) ∧ (p0 ∨ True)) ∧ ((p7 ∨ True) ∨ (False ∨ p0))) → (((p0 → False) → False) ∧ ((p4 ∨ p2) ∧ (p3 ∧ p7)))) ∧ ((((False ∧ True) ∨ (p7 → p7)) → False) ∧ (((p3 → False) ∧ (p0 → False)) ∧ ((False ∨ p0) → (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_30 : ((False ∧ True) ∨ (p7 → p7)) := by
            apply Or.inr
            intro assump_24
            exact assump_24
          let assump_23 := assump_6 assump_30
          apply False.elim assump_23


variable (p4 p3 p5 p2 p7 p1 p0 : Prop)
theorem file6_132486 : ((((((p3 → p5) → False) ∧ ((p4 ∨ p1) ∨ (p0 → False))) → False) ∧ ((((False ∨ p2) ∨ (p2 ∨ p2)) ∨ ((p5 → True) → False)) ∧ (((p7 → False) → (False → False)) ∧ ((p1 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              have assump_70 : (p1 → True) := by
                intro assump_25
                apply True.intro
              let assump_24 := assump_19 assump_70
              apply False.elim assump_24
        case inr assump_11 =>
          cases assump_11
          case inl assump_29 =>
            cases assump_7
            case intro assump_33 assump_34 =>
              have assump_71 : (p1 → True) := by
                intro assump_40
                apply True.intro
              let assump_39 := assump_34 assump_71
              apply False.elim assump_39
          case inr assump_30 =>
            cases assump_7
            case intro assump_46 assump_47 =>
              have assump_72 : (p1 → True) := by
                intro assump_53
                apply True.intro
              let assump_52 := assump_47 assump_72
              apply False.elim assump_52
      case inr assump_9 =>
        cases assump_7
        case intro assump_59 assump_60 =>
          have assump_73 : (p1 → True) := by
            intro assump_66
            apply True.intro
          let assump_65 := assump_60 assump_73
          apply False.elim assump_65


variable (p7 p0 p5 p4 p2 : Prop)
theorem file6_134328 : ((((((p0 ∨ p2) → False) → False) → (((False → p5) → (False → False)) → False)) ∧ ((((p7 ∨ True) ∧ (False → False)) → False) ∧ (((p7 ∨ p4) ∧ (p2 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_20 : ((p7 ∨ True) ∧ (False → False)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_20
      apply False.elim assump_13


variable (p3 p7 p6 p1 p4 p5 : Prop)
theorem file6_134953 : (((((p4 → False) → (p5 ∨ True)) → False) → False) → ((((p1 → p7) ∧ (False ∧ p3)) ∧ ((p6 ∨ p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p5 p7 p0 p2 p4 : Prop)
theorem file6_135364 : (((((p7 ∨ p0) ∨ (p7 ∨ False)) ∨ ((False ∧ p4) → (p2 → False))) → False) → ((((p4 ∨ p5) → False) → False) ∧ (((True ∧ p5) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_36 : (((p7 ∨ p0) ∨ (p7 ∨ False)) ∨ ((False ∧ p4) → (p2 → False))) := by
    apply Or.inr
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_7 := assump_1 assump_36
  apply False.elim assump_7
  intro assump_19
  have assump_37 : (((p7 ∨ p0) ∨ (p7 ∨ False)) ∨ ((False ∧ p4) → (p2 → False))) := by
    apply Or.inr
    intro assump_25
    intro assump_26
    cases assump_25
    case intro assump_29 assump_30 =>
      apply False.elim assump_29
  let assump_24 := assump_1 assump_37
  apply False.elim assump_24


variable (p1 p3 p0 p4 p2 p5 p7 p6 : Prop)
theorem file6_136244 : ((((((p7 → False) ∧ (p6 ∨ p7)) ∧ ((p1 ∨ p5) → False)) ∧ (((p6 → p5) → False) ∧ ((False → False) → False))) ∧ ((((p0 ∨ p6) ∨ (p2 → False)) ∨ ((p7 ∨ False) → (p5 → p7))) ∨ (((p3 ∨ p4) ∧ (p1 → False)) ∨ ((True ∧ p2) ∧ (True ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_3
              case inl assump_24 =>
                cases assump_24
                case inl assump_26 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_28
                    case inl assump_30 =>
                      have assump_241 : (False → False) := by
                        intro assump_36
                        apply False.elim assump_36
                      let assump_35 := assump_19 assump_241
                      apply False.elim assump_35
                    case inr assump_31 =>
                      have assump_242 : (False → False) := by
                        intro assump_46
                        apply False.elim assump_46
                      let assump_45 := assump_19 assump_242
                      apply False.elim assump_45
                  case inr assump_29 =>
                    have assump_243 : (False → False) := by
                      intro assump_56
                      apply False.elim assump_56
                    let assump_55 := assump_19 assump_243
                    apply False.elim assump_55
                case inr assump_27 =>
                  have assump_244 : (False → False) := by
                    intro assump_66
                    apply False.elim assump_66
                  let assump_65 := assump_19 assump_244
                  apply False.elim assump_65
              case inr assump_25 =>
                cases assump_25
                case inl assump_72 =>
                  cases assump_72
                  case intro assump_74 assump_75 =>
                    cases assump_74
                    case inl assump_76 =>
                      have assump_245 : (False → False) := by
                        intro assump_85
                        apply False.elim assump_85
                      let assump_84 := assump_19 assump_245
                      apply False.elim assump_84
                    case inr assump_77 =>
                      have assump_246 : (False → False) := by
                        intro assump_98
                        apply False.elim assump_98
                      let assump_97 := assump_19 assump_246
                      apply False.elim assump_97
                case inr assump_73 =>
                  cases assump_73
                  case intro assump_104 assump_105 =>
                    cases assump_104
                    case intro assump_106 assump_107 =>
                      cases assump_105
                      case intro assump_112 assump_113 =>
                        have assump_247 : (False → False) := by
                          intro assump_121
                          apply False.elim assump_121
                        let assump_120 := assump_19 assump_247
                        apply False.elim assump_120
          case inr assump_13 =>
            cases assump_5
            case intro assump_131 assump_132 =>
              cases assump_3
              case inl assump_137 =>
                cases assump_137
                case inl assump_139 =>
                  cases assump_139
                  case inl assump_141 =>
                    cases assump_141
                    case inl assump_143 =>
                      have assump_248 : (False → False) := by
                        intro assump_149
                        apply False.elim assump_149
                      let assump_148 := assump_132 assump_248
                      apply False.elim assump_148
                    case inr assump_144 =>
                      have assump_249 : (False → False) := by
                        intro assump_159
                        apply False.elim assump_159
                      let assump_158 := assump_132 assump_249
                      apply False.elim assump_158
                  case inr assump_142 =>
                    have assump_250 : (False → False) := by
                      intro assump_169
                      apply False.elim assump_169
                    let assump_168 := assump_132 assump_250
                    apply False.elim assump_168
                case inr assump_140 =>
                  have assump_251 : (False → False) := by
                    intro assump_180
                    apply False.elim assump_180
                  let assump_179 := assump_132 assump_251
                  apply False.elim assump_179
              case inr assump_138 =>
                cases assump_138
                case inl assump_186 =>
                  cases assump_186
                  case intro assump_188 assump_189 =>
                    cases assump_188
                    case inl assump_190 =>
                      have assump_252 : (False → False) := by
                        intro assump_199
                        apply False.elim assump_199
                      let assump_198 := assump_132 assump_252
                      apply False.elim assump_198
                    case inr assump_191 =>
                      have assump_253 : (False → False) := by
                        intro assump_212
                        apply False.elim assump_212
                      let assump_211 := assump_132 assump_253
                      apply False.elim assump_211
                case inr assump_187 =>
                  cases assump_187
                  case intro assump_218 assump_219 =>
                    cases assump_218
                    case intro assump_220 assump_221 =>
                      cases assump_219
                      case intro assump_226 assump_227 =>
                        have assump_254 : (False → False) := by
                          intro assump_235
                          apply False.elim assump_235
                        let assump_234 := assump_132 assump_254
                        apply False.elim assump_234


variable (p3 p0 p7 p5 p4 p6 : Prop)
theorem file6_142790 : ((((((True ∨ p7) → (p3 ∨ True)) → False) → (((p6 → False) → False) ∧ ((p0 → p5) → (p4 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_41 : ((((True ∨ p7) → (p3 ∨ True)) → False) → (((p6 → False) → False) ∧ ((p0 → p5) → (p4 ∨ p6)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_42 : ((True ∨ p7) → (p3 ∨ True)) := by
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        apply Or.inr
        apply True.intro
      case inr assump_14 =>
        apply Or.inr
        apply True.intro
    let assump_11 := assump_5 assump_42
    apply False.elim assump_11
    intro assump_22
    have assump_43 : ((True ∨ p7) → (p3 ∨ True)) := by
      intro assump_28
      cases assump_28
      case inl assump_29 =>
        apply Or.inr
        apply True.intro
      case inr assump_30 =>
        apply Or.inr
        apply True.intro
    let assump_27 := assump_5 assump_43
    apply False.elim assump_27
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p5 p6 : Prop)
theorem file6_143871 : (((((p6 → False) ∧ (False ∧ p5)) → False) ∧ (((False ∨ False) → (False → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : ((False ∨ False) → (False → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_3 assump_14
    apply False.elim assump_8


variable (p6 p5 p2 p3 p1 p0 p4 p7 : Prop)
theorem file6_144307 : ((((((p5 ∨ p0) ∨ (p7 → False)) ∧ ((p2 → p1) → (p3 ∧ p1))) ∧ (((p7 ∧ False) → False) → False)) ∧ ((((p0 ∧ p6) → (p2 ∧ p0)) ∧ ((p7 ∧ p7) ∧ (p2 → p1))) ∧ (((p4 → False) ∧ (p3 ∧ True)) ∧ ((p2 ∧ False) → False)))) → False) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_6
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                cases assump_24
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case intro assump_29 assump_30 =>
                    cases assump_22
                    case intro assump_37 assump_38 =>
                      cases assump_37
                      case intro assump_39 assump_40 =>
                        cases assump_40
                        case intro assump_43 assump_44 =>
                          have assump_177 : ((p7 ∧ False) → False) := by
                            intro assump_59
                            cases assump_59
                            case intro assump_60 assump_61 =>
                              apply False.elim assump_61
                          let assump_58 := assump_8 assump_177
                          apply False.elim assump_58
          case inr assump_14 =>
            cases assump_6
            case intro assump_75 assump_76 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                cases assump_78
                case intro assump_81 assump_82 =>
                  cases assump_81
                  case intro assump_83 assump_84 =>
                    cases assump_76
                    case intro assump_91 assump_92 =>
                      cases assump_91
                      case intro assump_93 assump_94 =>
                        cases assump_94
                        case intro assump_97 assump_98 =>
                          have assump_178 : ((p7 ∧ False) → False) := by
                            intro assump_113
                            cases assump_113
                            case intro assump_114 assump_115 =>
                              apply False.elim assump_115
                          let assump_112 := assump_8 assump_178
                          apply False.elim assump_112
        case inr assump_12 =>
          cases assump_6
          case intro assump_129 assump_130 =>
            cases assump_129
            case intro assump_131 assump_132 =>
              cases assump_132
              case intro assump_135 assump_136 =>
                cases assump_135
                case intro assump_137 assump_138 =>
                  cases assump_130
                  case intro assump_145 assump_146 =>
                    cases assump_145
                    case intro assump_147 assump_148 =>
                      cases assump_148
                      case intro assump_151 assump_152 =>
                        have assump_179 : ((p7 ∧ False) → False) := by
                          intro assump_167
                          cases assump_167
                          case intro assump_168 assump_169 =>
                            apply False.elim assump_169
                        let assump_166 := assump_8 assump_179
                        apply False.elim assump_166


variable (p6 p4 p0 p3 p2 p1 : Prop)
theorem file6_147930 : (((((False ∧ True) ∧ (p4 ∧ p4)) → ((p6 → False) → (p3 → True))) ∨ (((p2 ∧ False) → False) ∨ ((p6 ∧ True) → (p1 ∧ p6)))) ∨ ((((p0 → False) ∨ (p6 → True)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p6 p4 p3 p5 p7 p1 p2 p0 : Prop)
theorem file6_148274 : (((((p0 ∨ p6) ∧ (True → False)) → ((p6 → False) → False)) ∧ (((p3 → p3) ∨ (p3 → p0)) ∨ ((p0 ∧ False) → (p4 ∨ p2)))) ∨ ((((p5 ∧ p2) ∨ (p1 → False)) ∧ ((p4 ∧ True) ∨ (True → False))) ∨ (((p1 → p2) → (p7 ∧ p3)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_28 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_28
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_29 : True := by
        apply True.intro
      let assump_21 := assump_6 assump_29
      apply False.elim assump_21
  apply Or.inl
  apply Or.inl
  intro assump_25
  exact assump_25


variable (p6 p0 p3 p1 p5 p7 p2 p4 : Prop)
theorem file6_149086 : ((((((p3 → False) ∧ (p7 → p6)) → ((False ∧ True) → (p7 → False))) → False) ∨ ((((p4 → True) ∧ (p3 → False)) → False) ∧ (((True → p2) ∧ (p0 ∧ p1)) ∧ ((p5 ∨ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_55 : (((p3 → False) ∧ (p7 → p6)) → ((False ∧ True) → (p7 → False))) := by
      intro assump_7
      intro assump_8
      intro assump_9
      cases assump_8
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
    let assump_6 := assump_2 assump_55
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            have assump_56 : ((p4 → True) ∧ (p3 → False)) := by
              apply And.intro
              intro assump_43
              apply True.intro
              intro assump_44
              have assump_57 : (p5 ∨ p3) := by
                apply Or.inr
                exact assump_44
              let assump_48 := assump_24 assump_57
              apply False.elim assump_48
            let assump_42 := assump_19 assump_56
            apply False.elim assump_42


