variable (p4 p5 p6 p3 p7 : Prop)
theorem file32_41 : (((((False ∨ p7) ∨ (False → False)) → False) → False) ∨ ((((p3 → False) → False) → False) ∧ (((p6 → p6) ∧ (p5 ∧ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False ∨ p7) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p1 : Prop)
theorem file32_444 : ((((((p1 ∨ p3) → False) → False) → False) ∧ ((((False → p3) → False) → False) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_30 : (((False → p3) → False) → False) := by
      intro assump_17
      have assump_31 : (False → p3) := by
        intro assump_21
        apply False.elim assump_21
      let assump_20 := assump_17 assump_31
      apply False.elim assump_20
    let assump_16 := assump_11 assump_30
    apply False.elim assump_16


variable (p0 p3 : Prop)
theorem file32_996 : ((((((False → False) ∨ (p0 ∨ p3)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∨ (p0 ∨ p3)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∨ (p0 ∨ p3)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p3 p4 p7 p1 p5 : Prop)
theorem file32_1506 : (((((p3 ∨ False) → False) ∧ ((False → False) → False)) → (((p1 ∧ False) ∨ (p5 → False)) → False)) ∨ ((((p0 ∨ True) ∨ (False ∨ p7)) ∧ ((p3 → p4) ∧ (p3 ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      have assump_26 : (False → False) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_14 assump_26
      apply False.elim assump_19


variable (p4 p0 p7 p2 p1 p6 p3 : Prop)
theorem file32_2179 : (((((False → p0) ∨ (p7 ∧ p3)) → False) → (((p3 → False) → (p3 ∧ False)) → False)) ∨ ((((p1 ∨ p7) ∨ (p1 → p2)) → ((p4 ∧ True) ∨ (p0 ∨ p6))) ∧ (((p2 ∨ False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : ((False → p0) ∨ (p7 ∧ p3)) := by
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p1 p5 p0 p3 p2 p6 : Prop)
theorem file32_2653 : (((((p3 → p2) → (p0 → False)) ∧ ((False → p1) → False)) → (((p3 ∨ False) → False) → False)) ∧ ((((p3 → False) ∧ (p5 ∧ True)) → False) → (((p6 ∧ p3) ∧ (p6 ∧ False)) → ((True → False) → False)))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_37 : (False → p1) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_6 assump_37
    apply False.elim assump_11
  intro assump_18
  intro assump_19
  intro assump_20
  cases assump_19
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_24
      case intro assump_31 assump_32 =>
        apply False.elim assump_32


variable (p5 p4 p1 p3 p2 p7 p6 : Prop)
theorem file32_3448 : ((((((p6 → True) → (p7 → p3)) ∧ ((p2 → False) → (True → False))) ∨ (((p3 ∧ p7) ∨ (p4 → False)) ∨ ((True ∨ True) ∨ (p4 ∨ p1)))) ∧ ((((p7 → False) → False) ∧ ((False ∨ p1) → False)) ∧ (((p5 ∨ p6) ∨ (p1 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_157 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
              apply Or.inr
              intro assump_23
              exact assump_23
            let assump_22 := assump_13 assump_157
            apply False.elim assump_22
    case inr assump_5 =>
      cases assump_5
      case inl assump_29 =>
        cases assump_29
        case inl assump_31 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            cases assump_3
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                have assump_158 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                  apply Or.inr
                  intro assump_50
                  exact assump_50
                let assump_49 := assump_40 assump_158
                apply False.elim assump_49
        case inr assump_32 =>
          cases assump_3
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              have assump_159 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                apply Or.inr
                intro assump_69
                exact assump_69
              let assump_68 := assump_59 assump_159
              apply False.elim assump_68
      case inr assump_30 =>
        cases assump_30
        case inl assump_75 =>
          cases assump_75
          case inl assump_77 =>
            cases assump_3
            case intro assump_81 assump_82 =>
              cases assump_81
              case intro assump_83 assump_84 =>
                have assump_160 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                  apply Or.inr
                  intro assump_92
                  exact assump_92
                let assump_91 := assump_82 assump_160
                apply False.elim assump_91
          case inr assump_78 =>
            cases assump_3
            case intro assump_100 assump_101 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                have assump_161 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                  apply Or.inr
                  intro assump_111
                  exact assump_111
                let assump_110 := assump_101 assump_161
                apply False.elim assump_110
        case inr assump_76 =>
          cases assump_76
          case inl assump_117 =>
            cases assump_3
            case intro assump_121 assump_122 =>
              cases assump_121
              case intro assump_123 assump_124 =>
                have assump_162 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                  apply Or.inr
                  intro assump_132
                  exact assump_132
                let assump_131 := assump_122 assump_162
                apply False.elim assump_131
          case inr assump_118 =>
            cases assump_3
            case intro assump_140 assump_141 =>
              cases assump_140
              case intro assump_142 assump_143 =>
                have assump_163 : ((p5 ∨ p6) ∨ (p1 → p1)) := by
                  apply Or.inr
                  intro assump_151
                  exact assump_151
                let assump_150 := assump_141 assump_163
                apply False.elim assump_150


variable (p3 p2 p5 p0 p7 p4 p6 : Prop)
theorem file32_7284 : ((((((p7 ∧ p4) → (p2 → False)) → ((p2 ∧ False) → False)) ∨ (((p5 → p5) ∧ (p6 → False)) ∨ ((p3 ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 ∧ p4) → (p2 → False)) → ((p2 ∧ False) → False)) ∨ (((p5 → p5) ∧ (p6 → False)) ∨ ((p3 ∨ p0) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p0 p6 p3 p2 : Prop)
theorem file32_7834 : (((((p2 ∨ True) ∨ (p3 ∧ p0)) → False) → False) ∨ ((((p6 ∨ p6) → False) → ((p0 → p4) → False)) ∨ (((p4 ∧ p4) ∨ (p4 ∧ p6)) ∨ ((False ∨ p6) ∨ (False → False))))) := by
  apply Or.inl
  intro assump_9
  have assump_16 : ((p2 ∨ True) ∨ (p3 ∧ p0)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_12 := assump_9 assump_16
  apply False.elim assump_12


variable (p0 p3 p4 p1 p2 p6 p5 : Prop)
theorem file32_8267 : ((((((p2 ∧ p2) ∨ (p1 → p3)) ∨ ((p2 ∧ p3) ∧ (p2 ∨ True))) ∨ (((p4 ∧ p3) ∧ (p4 ∨ p6)) ∨ ((p2 ∨ p3) → False))) ∧ ((((p5 → p0) ∧ (p3 ∧ True)) ∧ ((p5 → False) → False)) ∧ (((False → False) → False) ∧ ((p2 → True) ∧ (p6 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  cases assump_21
                  case intro assump_24 assump_25 =>
                    cases assump_17
                    case intro assump_32 assump_33 =>
                      cases assump_33
                      case intro assump_36 assump_37 =>
                        cases assump_37
                        case intro assump_40 assump_41 =>
                          have assump_333 : (False → False) := by
                            intro assump_51
                            apply False.elim assump_51
                          let assump_50 := assump_32 assump_333
                          apply False.elim assump_50
        case inr assump_9 =>
          cases assump_3
          case intro assump_59 assump_60 =>
            cases assump_59
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_64
                case intro assump_67 assump_68 =>
                  cases assump_60
                  case intro assump_75 assump_76 =>
                    cases assump_76
                    case intro assump_79 assump_80 =>
                      cases assump_80
                      case intro assump_83 assump_84 =>
                        have assump_334 : (False → False) := by
                          intro assump_93
                          apply False.elim assump_93
                        let assump_92 := assump_75 assump_334
                        apply False.elim assump_92
      case inr assump_7 =>
        cases assump_7
        case intro assump_99 assump_100 =>
          cases assump_99
          case intro assump_101 assump_102 =>
            cases assump_100
            case inl assump_107 =>
              cases assump_3
              case intro assump_111 assump_112 =>
                cases assump_111
                case intro assump_113 assump_114 =>
                  cases assump_113
                  case intro assump_115 assump_116 =>
                    cases assump_116
                    case intro assump_119 assump_120 =>
                      cases assump_112
                      case intro assump_127 assump_128 =>
                        cases assump_128
                        case intro assump_131 assump_132 =>
                          cases assump_132
                          case intro assump_135 assump_136 =>
                            have assump_335 : (False → False) := by
                              intro assump_146
                              apply False.elim assump_146
                            let assump_145 := assump_127 assump_335
                            apply False.elim assump_145
            case inr assump_108 =>
              cases assump_3
              case intro assump_154 assump_155 =>
                cases assump_154
                case intro assump_156 assump_157 =>
                  cases assump_156
                  case intro assump_158 assump_159 =>
                    cases assump_159
                    case intro assump_162 assump_163 =>
                      cases assump_155
                      case intro assump_170 assump_171 =>
                        cases assump_171
                        case intro assump_174 assump_175 =>
                          cases assump_175
                          case intro assump_178 assump_179 =>
                            have assump_336 : (False → False) := by
                              intro assump_189
                              apply False.elim assump_189
                            let assump_188 := assump_170 assump_336
                            apply False.elim assump_188
    case inr assump_5 =>
      cases assump_5
      case inl assump_195 =>
        cases assump_195
        case intro assump_197 assump_198 =>
          cases assump_197
          case intro assump_199 assump_200 =>
            cases assump_198
            case inl assump_205 =>
              cases assump_3
              case intro assump_209 assump_210 =>
                cases assump_209
                case intro assump_211 assump_212 =>
                  cases assump_211
                  case intro assump_213 assump_214 =>
                    cases assump_214
                    case intro assump_217 assump_218 =>
                      cases assump_210
                      case intro assump_225 assump_226 =>
                        cases assump_226
                        case intro assump_229 assump_230 =>
                          cases assump_230
                          case intro assump_233 assump_234 =>
                            have assump_337 : (False → False) := by
                              intro assump_243
                              apply False.elim assump_243
                            let assump_242 := assump_225 assump_337
                            apply False.elim assump_242
            case inr assump_206 =>
              cases assump_3
              case intro assump_251 assump_252 =>
                cases assump_251
                case intro assump_253 assump_254 =>
                  cases assump_253
                  case intro assump_255 assump_256 =>
                    cases assump_256
                    case intro assump_259 assump_260 =>
                      cases assump_252
                      case intro assump_267 assump_268 =>
                        cases assump_268
                        case intro assump_271 assump_272 =>
                          cases assump_272
                          case intro assump_275 assump_276 =>
                            have assump_338 : (False → False) := by
                              intro assump_285
                              apply False.elim assump_285
                            let assump_284 := assump_267 assump_338
                            apply False.elim assump_284
      case inr assump_196 =>
        cases assump_3
        case intro assump_293 assump_294 =>
          cases assump_293
          case intro assump_295 assump_296 =>
            cases assump_295
            case intro assump_297 assump_298 =>
              cases assump_298
              case intro assump_301 assump_302 =>
                cases assump_294
                case intro assump_309 assump_310 =>
                  cases assump_310
                  case intro assump_313 assump_314 =>
                    cases assump_314
                    case intro assump_317 assump_318 =>
                      have assump_339 : (False → False) := by
                        intro assump_327
                        apply False.elim assump_327
                      let assump_326 := assump_309 assump_339
                      apply False.elim assump_326


variable (p4 p3 p5 p0 p2 : Prop)
theorem file32_15826 : (((((p5 ∧ False) ∧ (True → False)) → False) → False) → ((((p0 ∨ True) → (p2 → False)) → ((p4 → False) ∨ (p5 ∨ p3))) → (((True → p5) ∧ (p5 → p4)) ∧ ((p3 → p2) → (p0 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  have assump_66 : (((p5 ∧ False) ∧ (True → False)) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
  let assump_10 := assump_1 assump_66
  apply False.elim assump_10
  intro assump_23
  have assump_67 : (((p5 ∧ False) ∧ (True → False)) → False) := by
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        apply False.elim assump_35
  let assump_30 := assump_1 assump_67
  apply False.elim assump_30
  intro assump_43
  intro assump_44
  have assump_68 : (((p5 ∧ False) ∧ (True → False)) → False) := by
    intro assump_54
    cases assump_54
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        apply False.elim assump_58
  let assump_53 := assump_1 assump_68
  apply False.elim assump_53


variable (p6 p2 p0 p4 p3 p5 p1 : Prop)
theorem file32_17140 : (((((p6 ∨ True) ∨ (p0 ∧ True)) → ((False → p4) → False)) → False) ∨ ((((p4 → False) → False) ∨ ((p4 ∧ p1) ∧ (p5 → False))) → (((p5 ∨ p2) → False) → ((True ∧ p5) ∨ (p3 → p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p6 ∨ True) ∨ (p0 ∧ True)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_12
  have assump_13 : (False → p4) := by
    intro assump_6
    apply False.elim assump_6
  let assump_5 := assump_4 assump_13
  apply False.elim assump_5


variable (p2 p1 p0 p3 p4 p7 : Prop)
theorem file32_17712 : ((((((False ∨ p3) ∨ (p1 → False)) ∧ ((False ∧ p7) ∧ (p2 ∨ p1))) ∧ (((p0 → False) → False) ∨ ((p2 ∧ p7) → False))) ∧ ((((p3 → True) → (p7 → p4)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            apply False.elim assump_10
          case inr assump_11 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                apply False.elim assump_18
        case inr assump_9 =>
          cases assump_7
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_26


variable (p3 p5 p6 p2 p0 p1 : Prop)
theorem file32_18719 : ((((((False → p3) → False) → ((p2 ∨ p6) ∧ (p5 → False))) ∨ (((p1 ∧ p3) ∧ (p5 → False)) → ((p0 ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False → p3) → False) → ((p2 ∨ p6) ∧ (p5 → False))) ∨ (((p1 ∧ p3) ∧ (p5 → False)) → ((p0 ∨ p0) → False))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_31 : (False → p3) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_31
    apply False.elim assump_8
    intro assump_15
    have assump_32 : (False → p3) := by
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_5 assump_32
    apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p3 p2 p7 p0 p4 : Prop)
theorem file32_19531 : ((((((False ∨ p4) ∧ (False → False)) → ((p3 ∨ p0) ∧ (p2 → False))) → (((p3 ∨ p7) → (False ∨ False)) → ((p4 → False) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False ∨ p4) ∧ (False → False)) → ((p3 ∨ p0) ∧ (p2 → False))) → (((p3 ∨ p7) → (False ∨ False)) → ((p4 → False) → (p3 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    have assump_30 : (p3 ∨ p7) := by
      apply Or.inl
      exact assump_8
    let assump_18 := assump_6 assump_30
    cases assump_18
    case inl assump_20 =>
      apply False.elim assump_20
    case inr assump_21 =>
      apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p6 p5 p4 p1 : Prop)
theorem file32_20316 : (((((True ∨ p4) ∨ (p1 → False)) ∨ ((p2 ∨ p5) ∨ (p6 ∨ p5))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p4) ∨ (p1 → False)) ∨ ((p2 ∨ p5) ∨ (p6 ∨ p5))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p0 p3 p1 p7 p5 : Prop)
theorem file32_20693 : (((((False ∧ p2) ∨ (p5 ∨ p1)) ∨ ((False → False) ∧ (p3 ∧ p7))) ∧ (((True ∨ p0) → (False → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8
      case inr assump_7 =>
        cases assump_7
        case inl assump_12 =>
          have assump_52 : ((True ∨ p0) → (False → True)) := by
            intro assump_19
            intro assump_20
            apply True.intro
          let assump_18 := assump_3 assump_52
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_53 : ((True ∨ p0) → (False → True)) := by
            intro assump_29
            intro assump_30
            apply True.intro
          let assump_28 := assump_3 assump_53
          apply False.elim assump_28
    case inr assump_5 =>
      cases assump_5
      case intro assump_34 assump_35 =>
        cases assump_35
        case intro assump_38 assump_39 =>
          have assump_54 : ((True ∨ p0) → (False → True)) := by
            intro assump_47
            intro assump_48
            apply True.intro
          let assump_46 := assump_3 assump_54
          apply False.elim assump_46


variable (p4 p5 p2 p3 p6 p1 : Prop)
theorem file32_22092 : (((((p1 ∨ True) ∧ (p3 ∧ False)) → False) ∨ (((p2 → False) ∧ (p6 → False)) → False)) ∨ ((((p4 → p4) → False) → ((p5 → False) ∨ (True ∧ p2))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply False.elim assump_17


variable (p0 p1 p7 p5 p3 p2 p4 : Prop)
theorem file32_22667 : (((((p0 ∧ p0) → (False → False)) → False) → (((True → False) ∧ (p4 ∧ False)) → ((p0 → p2) ∨ (p0 ∨ False)))) ∨ ((((p5 → False) → False) ∨ ((p0 → p4) → (p3 → p7))) ∨ (((p1 ∧ p4) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p2 p7 p4 p1 : Prop)
theorem file32_23110 : (((((p1 ∧ p1) → False) → ((p4 ∧ False) → (p7 → False))) ∧ (((p4 → True) → False) ∧ ((p2 → p1) ∨ (p1 → p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_28 : (p4 → True) := by
          intro assump_16
          apply True.intro
        let assump_15 := assump_6 assump_28
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_29 : (p4 → True) := by
          intro assump_24
          apply True.intro
        let assump_23 := assump_6 assump_29
        apply False.elim assump_23


variable (p5 p6 p3 : Prop)
theorem file32_23835 : (((((p5 → p5) → False) ∧ ((p3 ∧ p3) ∧ (p6 ∨ False))) ∧ (((False → False) → (p3 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case inl assump_16 =>
            have assump_34 : ((False → False) → (p3 → p6)) := by
              intro assump_23
              intro assump_24
              exact assump_16
            let assump_22 := assump_3 assump_34
            apply False.elim assump_22
          case inr assump_17 =>
            apply False.elim assump_17


variable (p3 p6 p0 p5 p4 p7 p2 : Prop)
theorem file32_24626 : ((((((p6 → True) ∧ (p6 → False)) ∧ ((p3 ∨ p0) ∧ (p0 ∧ p3))) → (((False → False) → False) → ((p7 → False) → (p5 → False)))) ∧ ((((True → p0) → (p2 ∧ p2)) → ((p4 → p5) → (False ∨ True))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_24 : (((True → p0) → (p2 ∧ p2)) → ((p4 → p5) → (False ∨ True))) := by
      intro assump_15
      intro assump_16
      apply Or.inr
      apply True.intro
    let assump_14 := assump_9 assump_24
    apply False.elim assump_14


variable (p1 p4 p3 p5 : Prop)
theorem file32_25201 : (((((p1 ∨ p4) ∧ (True → False)) → ((p1 ∧ p1) → False)) → False) → ((((p3 → False) ∧ (p5 → False)) → ((p5 → False) ∨ (p4 ∨ p3))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_39 : (((p1 ∨ p4) ∧ (True → False)) → ((p1 ∧ p1) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          have assump_40 : True := by
            apply True.intro
          let assump_24 := assump_17 assump_40
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_41 : True := by
            apply True.intro
          let assump_32 := assump_17 assump_41
          apply False.elim assump_32
  let assump_7 := assump_1 assump_39
  apply False.elim assump_7


variable (p2 p4 p7 p0 p1 p6 p5 : Prop)
theorem file32_26127 : (((((p2 → False) → (False → False)) → False) → (((False → p7) → (p4 ∧ p5)) → ((p6 → False) → False))) ∨ ((((p0 → p5) ∧ (p6 → p4)) → ((p2 ∨ p1) → False)) ∧ (((False ∨ p0) → (p6 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_18 : ((p2 → False) → (False → False)) := by
    intro assump_11
    intro assump_12
    apply False.elim assump_12
  let assump_10 := assump_1 assump_18
  apply False.elim assump_10


variable (p0 p7 p3 p5 p1 p6 p4 : Prop)
theorem file32_26655 : (((((p6 ∧ False) → (p6 → p7)) → False) → False) ∨ ((((p3 → False) ∨ (p7 ∧ p0)) → ((p0 → False) ∨ (p1 → p3))) → (((p7 → False) ∧ (p4 → p3)) → ((p7 ∧ p5) → (p5 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p6 ∧ False) → (p6 → p7)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p6 p1 p4 p0 p5 p2 : Prop)
theorem file32_27170 : (((((p6 → False) ∧ (p0 → False)) → False) ∨ (((p5 → False) ∨ (p4 → p4)) ∨ ((p4 → p2) ∧ (p6 ∧ p2)))) → ((((p0 → False) ∧ (True → False)) → ((p2 → p0) → (False → False))) ∨ (((p7 → False) → (p1 → False)) ∨ ((p7 → False) ∧ (p7 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  case inr assump_3 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        intro assump_18
        intro assump_19
        apply False.elim assump_19
      case inr assump_14 =>
        apply Or.inl
        intro assump_24
        intro assump_25
        intro assump_26
        apply False.elim assump_26
    case inr assump_12 =>
      cases assump_12
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          apply Or.inl
          intro assump_39
          intro assump_40
          intro assump_41
          apply False.elim assump_41


variable (p5 p3 p6 p4 : Prop)
theorem file32_28322 : (((((False → p3) ∨ (p4 → False)) ∨ ((False ∨ p5) → (p6 ∧ False))) → False) → False) := by
  intro assump_7
  have assump_17 : (((False → p3) ∨ (p4 → False)) ∨ ((False ∨ p5) → (p6 ∧ False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p3 p1 p4 p5 p0 p6 : Prop)
theorem file32_28730 : (((((p4 ∨ p3) ∧ (p6 → False)) → ((p1 → p1) ∧ (p4 ∨ p5))) → (((False ∧ p6) → False) ∨ ((p6 → False) ∧ (p3 ∧ p0)))) ∨ ((((True ∨ p6) → False) ∧ ((p4 → False) → (True ∧ True))) → (((p1 ∨ p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p1 p7 p0 p3 p4 p5 p2 : Prop)
theorem file32_29152 : (((((False ∨ p7) ∧ (p2 → False)) → ((True ∨ p5) → (p2 → p3))) ∨ (((p1 ∨ True) ∧ (p3 ∧ p3)) → ((p3 ∨ p4) ∨ (True ∨ True)))) ∨ ((((p3 → False) → False) → False) ∧ (((p1 → False) ∧ (False ∧ True)) ∨ ((p7 ∨ p0) ∨ (p4 ∧ p1))))) := by
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
      case inl assump_12 =>
        apply False.elim assump_12
      case inr assump_13 =>
        have assump_40 : p2 := by
          exact assump_3
        let assump_20 := assump_11 assump_40
        apply False.elim assump_20
  case inr assump_7 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        apply False.elim assump_28
      case inr assump_29 =>
        have assump_41 : p2 := by
          exact assump_3
        let assump_36 := assump_27 assump_41
        apply False.elim assump_36


variable (p1 p2 p0 p3 p6 p5 : Prop)
theorem file32_30203 : ((((((p0 → False) ∧ (p0 ∧ p6)) → False) → (((True ∨ p0) → False) ∧ ((p3 → False) ∧ (p1 → False)))) ∧ ((((p2 ∨ p1) ∧ (True → False)) → False) ∨ (((p0 ∧ True) → (p0 → False)) ∧ ((True → False) ∨ (p0 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_83 : (((p0 → False) ∧ (p0 ∧ p6)) → False) := by
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            have assump_84 : p0 := by
              exact assump_17
            let assump_25 := assump_13 assump_84
            apply False.elim assump_25
      let assump_11 := assump_2 assump_83
      let assump_29 := And.left assump_11
      have assump_85 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_30 := assump_29 assump_85
      apply False.elim assump_30
    case inr assump_7 =>
      cases assump_7
      case intro assump_34 assump_35 =>
        cases assump_35
        case inl assump_38 =>
          have assump_86 : True := by
            apply True.intro
          let assump_42 := assump_38 assump_86
          apply False.elim assump_42
        case inr assump_39 =>
          cases assump_39
          case inl assump_46 =>
            have assump_87 : (p0 ∧ True) := by
              apply And.intro
              exact assump_46
              apply True.intro
            let assump_51 := assump_34 assump_87
            have assump_88 : p0 := by
              exact assump_46
            let assump_52 := assump_51 assump_88
            apply False.elim assump_52
          case inr assump_47 =>
            have assump_89 : (((p0 → False) ∧ (p0 ∧ p6)) → False) := by
              intro assump_61
              cases assump_61
              case intro assump_62 assump_63 =>
                cases assump_63
                case intro assump_66 assump_67 =>
                  have assump_90 : p0 := by
                    exact assump_66
                  let assump_74 := assump_62 assump_90
                  apply False.elim assump_74
            let assump_60 := assump_2 assump_89
            let assump_78 := And.left assump_60
            have assump_91 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_79 := assump_78 assump_91
            apply False.elim assump_79


variable (p7 : Prop)
theorem file32_32696 : (((((p7 → False) ∧ (True → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : (((p7 → False) ∧ (True → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p6 p0 p4 p3 p1 p7 : Prop)
theorem file32_33184 : (((((p5 ∧ False) ∧ (p7 → p3)) → False) ∧ (((True ∧ p1) → (True ∨ p3)) ∨ ((p6 → False) → (p3 ∨ p6)))) ∨ ((((p0 → False) ∧ (p5 → p4)) → ((False → False) → (p0 ∧ True))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5
  apply Or.inl
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply Or.inl
    apply True.intro


variable (p6 p7 p4 p2 p3 p0 p5 : Prop)
theorem file32_33743 : (((((False ∧ p4) ∧ (p3 → False)) → ((p7 ∨ p5) ∧ (p3 → p2))) ∨ (((True → p6) → (p5 ∧ False)) ∧ ((p0 ∧ p3) → False))) ∧ ((((p4 ∨ p4) ∧ (p6 ∨ p7)) ∧ ((p0 → False) ∨ (p5 ∨ True))) → (((p5 → False) ∨ (p3 → False)) → ((True ∨ p2) ∨ (True → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_7
  apply And.intro
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  intro assump_14
  cases assump_7
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      apply False.elim assump_19
  intro assump_23
  intro assump_24
  cases assump_24
  case inl assump_25 =>
    cases assump_23
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_31
        case inl assump_33 =>
          cases assump_32
          case inl assump_37 =>
            cases assump_30
            case inl assump_41 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_42 =>
              cases assump_42
              case inl assump_45 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_46 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_38 =>
            cases assump_30
            case inl assump_53 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_54 =>
              cases assump_54
              case inl assump_57 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_58 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
        case inr assump_34 =>
          cases assump_32
          case inl assump_65 =>
            cases assump_30
            case inl assump_69 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_70 =>
              cases assump_70
              case inl assump_73 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_74 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_66 =>
            cases assump_30
            case inl assump_81 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_82 =>
              cases assump_82
              case inl assump_85 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_86 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
  case inr assump_26 =>
    cases assump_23
    case intro assump_93 assump_94 =>
      cases assump_93
      case intro assump_95 assump_96 =>
        cases assump_95
        case inl assump_97 =>
          cases assump_96
          case inl assump_101 =>
            cases assump_94
            case inl assump_105 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_106 =>
              cases assump_106
              case inl assump_109 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_110 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_102 =>
            cases assump_94
            case inl assump_117 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_118 =>
              cases assump_118
              case inl assump_121 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_122 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
        case inr assump_98 =>
          cases assump_96
          case inl assump_129 =>
            cases assump_94
            case inl assump_133 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_134 =>
              cases assump_134
              case inl assump_137 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_138 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_130 =>
            cases assump_94
            case inl assump_145 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_146 =>
              cases assump_146
              case inl assump_149 =>
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_150 =>
                apply Or.inl
                apply Or.inl
                apply True.intro


variable (p7 p3 p4 p5 p0 p1 p2 p6 : Prop)
theorem file32_39045 : (((((p2 ∧ p7) → False) ∧ ((False → p7) ∧ (True → False))) → (((False ∨ True) ∧ (p0 → p7)) ∨ ((p6 → False) ∨ (True → False)))) ∨ ((((p3 ∧ p4) ∧ (p7 ∧ p7)) ∨ ((p5 ∧ p0) → (p7 ∧ p5))) ∨ (((p1 ∨ True) → False) ∨ ((p0 → p1) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply And.intro
      apply Or.inr
      apply True.intro
      intro assump_12
      have assump_20 : True := by
        apply True.intro
      let assump_16 := assump_7 assump_20
      apply False.elim assump_16


variable (p5 p1 p4 p7 p3 : Prop)
theorem file32_39716 : (((((False → p4) → False) → False) ∨ (((False ∨ p7) ∧ (p7 → False)) → False)) ∨ ((((p7 ∨ p3) ∨ (p4 ∧ p3)) ∧ ((p3 ∧ p4) ∨ (p7 → p1))) ∧ (((True ∧ p7) ∨ (p4 ∧ p4)) ∧ ((p5 → False) ∨ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_14
  have assump_24 : (False → p4) := by
    intro assump_18
    apply False.elim assump_18
  let assump_17 := assump_14 assump_24
  apply False.elim assump_17


variable (p4 p5 p7 p0 p3 p6 p2 p1 : Prop)
theorem file32_40192 : (((((p0 → False) ∧ (False ∨ False)) ∧ ((False → False) → False)) ∧ (((p2 ∧ p6) → (p4 → p2)) → ((p0 → p0) → (p7 → p6)))) → ((((p2 ∨ p2) → (p7 ∨ p2)) ∨ ((False ∨ True) ∧ (p4 → False))) ∧ (((False ∨ True) ∧ (p7 ∨ p3)) ∨ ((p5 → p1) ∧ (p1 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          apply False.elim assump_11
  cases assump_1
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          apply False.elim assump_25


variable (p5 p4 p3 p0 p7 : Prop)
theorem file32_41187 : (((((p5 → p0) ∧ (p3 ∨ True)) → ((True → True) ∨ (p7 → False))) → False) → ((((p4 ∨ p7) ∧ (p7 → False)) ∧ ((p7 → False) → (p7 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        have assump_59 : (((p5 → p0) ∧ (p3 ∨ True)) → ((True → True) ∨ (p7 → False))) := by
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              apply Or.inl
              intro assump_27
              apply True.intro
            case inr assump_24 =>
              apply Or.inl
              intro assump_30
              apply True.intro
        let assump_17 := assump_1 assump_59
        apply False.elim assump_17
      case inr assump_8 =>
        have assump_60 : (((p5 → p0) ∧ (p3 ∨ True)) → ((True → True) ∨ (p7 → False))) := by
          intro assump_43
          cases assump_43
          case intro assump_44 assump_45 =>
            cases assump_45
            case inl assump_48 =>
              apply Or.inl
              intro assump_52
              apply True.intro
            case inr assump_49 =>
              apply Or.inl
              intro assump_55
              apply True.intro
        let assump_42 := assump_1 assump_60
        apply False.elim assump_42


variable (p3 p6 p4 : Prop)
theorem file32_42680 : (((((p6 ∨ False) → (False ∧ p3)) → ((p6 → False) → (p6 → False))) → (((p4 → False) → (p4 → False)) → False)) → False) := by
  intro assump_21
  have assump_53 : (((p6 ∨ False) → (False ∧ p3)) → ((p6 → False) → (p6 → False))) := by
    intro assump_25
    intro assump_26
    intro assump_27
    have assump_54 : (p6 ∨ False) := by
      apply Or.inl
      exact assump_27
    let assump_34 := assump_25 assump_54
    let assump_35 := And.left assump_34
    apply False.elim assump_35
  let assump_24 := assump_21 assump_53
  have assump_55 : ((p4 → False) → (p4 → False)) := by
    intro assump_40
    intro assump_41
    have assump_56 : p4 := by
      exact assump_41
    let assump_46 := assump_40 assump_56
    apply False.elim assump_46
  let assump_39 := assump_24 assump_55
  apply False.elim assump_39


variable (p7 p1 p0 p6 p2 p4 : Prop)
theorem file32_43550 : (((((p0 → False) ∨ (p7 → False)) ∨ ((False ∨ p6) ∧ (False ∨ True))) ∧ (((p1 ∧ p6) ∧ (p6 → False)) ∨ ((True → p6) ∨ (False ∧ False)))) → ((((False ∧ p4) ∧ (p2 ∨ p6)) ∧ ((p1 → False) → (p2 ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p1 p3 p0 : Prop)
theorem file32_44045 : (((((True → False) ∧ (p1 → p1)) → ((p3 ∧ p0) ∧ (False → False))) → False) → False) := by
  intro assump_1
  have assump_34 : (((True → False) ∧ (p1 → p1)) → ((p3 ∧ p0) ∧ (False → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_35 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_35
      apply False.elim assump_13
    cases assump_5
    case intro assump_17 assump_18 =>
      have assump_36 : True := by
        apply True.intro
      let assump_24 := assump_17 assump_36
      apply False.elim assump_24
    intro assump_28
    apply False.elim assump_28
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p4 p3 p5 : Prop)
theorem file32_44846 : (((((True ∧ False) → False) ∨ ((p5 ∨ p5) ∨ (p4 ∧ p3))) → False) → False) := by
  intro assump_5
  have assump_19 : (((True ∧ False) → False) ∨ ((p5 ∨ p5) ∨ (p4 ∧ p3))) := by
    apply Or.inl
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p7 p1 p4 p6 p3 : Prop)
theorem file32_45268 : (((((p1 → False) ∧ (True → False)) ∧ ((p3 ∧ p4) → False)) → (((True → p7) ∧ (p4 ∨ p3)) → False)) ∨ ((((p7 → p6) ∨ (False ∧ p4)) ∧ ((p7 → False) → False)) → False)) := by
  apply Or.inl
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
          have assump_43 : True := by
            apply True.intro
          let assump_22 := assump_14 assump_43
          apply False.elim assump_22
    case inr assump_8 =>
      cases assump_1
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          have assump_44 : True := by
            apply True.intro
          let assump_39 := assump_31 assump_44
          apply False.elim assump_39


variable (p1 p4 p7 p5 p6 p3 p0 p2 : Prop)
theorem file32_46229 : (((((p7 ∧ False) ∨ (p5 → False)) ∧ ((p6 → p6) → False)) ∨ (((p0 ∧ p2) → (p3 ∨ True)) → False)) → ((((p0 ∧ p4) → (p7 → True)) ∨ ((p5 ∨ p6) ∧ (p4 → False))) ∧ (((p4 → p1) → (p2 ∨ p3)) ∨ ((p0 ∧ p0) ∨ (p2 ∧ p7))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        apply Or.inl
        intro assump_18
        intro assump_19
        apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_22
    intro assump_23
    apply True.intro
  cases assump_1
  case inl assump_24 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          apply False.elim assump_31
      case inr assump_29 =>
        apply Or.inl
        intro assump_40
        have assump_68 : (p6 → p6) := by
          intro assump_45
          exact assump_45
        let assump_44 := assump_27 assump_68
        apply False.elim assump_44
  case inr assump_25 =>
    apply Or.inl
    intro assump_53
    have assump_69 : ((p0 ∧ p2) → (p3 ∨ True)) := by
      intro assump_58
      cases assump_58
      case intro assump_59 assump_60 =>
        apply Or.inr
        apply True.intro
    let assump_57 := assump_25 assump_69
    apply False.elim assump_57


variable (p7 p3 p0 p1 p5 p4 p2 : Prop)
theorem file32_47822 : ((((((False → p3) → (True → False)) ∨ ((False → False) → False)) ∧ (((p4 → False) ∧ (p5 → False)) ∨ ((p3 ∧ False) → False))) ∧ ((((p7 → False) → False) ∧ ((p1 ∨ p5) → (p7 → False))) ∧ (((p5 ∧ p1) ∧ (p4 ∧ p2)) ∧ ((p4 ∧ False) ∧ (p0 → p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_29
                      case intro assump_36 assump_37 =>
                        cases assump_27
                        case intro assump_42 assump_43 =>
                          cases assump_42
                          case intro assump_44 assump_45 =>
                            apply False.elim assump_45
        case inr assump_11 =>
          cases assump_3
          case intro assump_52 assump_53 =>
            cases assump_52
            case intro assump_54 assump_55 =>
              cases assump_53
              case intro assump_60 assump_61 =>
                cases assump_60
                case intro assump_62 assump_63 =>
                  cases assump_62
                  case intro assump_64 assump_65 =>
                    cases assump_63
                    case intro assump_70 assump_71 =>
                      cases assump_61
                      case intro assump_76 assump_77 =>
                        cases assump_76
                        case intro assump_78 assump_79 =>
                          apply False.elim assump_79
      case inr assump_7 =>
        cases assump_5
        case inl assump_86 =>
          cases assump_86
          case intro assump_88 assump_89 =>
            cases assump_3
            case intro assump_94 assump_95 =>
              cases assump_94
              case intro assump_96 assump_97 =>
                cases assump_95
                case intro assump_102 assump_103 =>
                  cases assump_102
                  case intro assump_104 assump_105 =>
                    cases assump_104
                    case intro assump_106 assump_107 =>
                      cases assump_105
                      case intro assump_112 assump_113 =>
                        cases assump_103
                        case intro assump_118 assump_119 =>
                          cases assump_118
                          case intro assump_120 assump_121 =>
                            apply False.elim assump_121
        case inr assump_87 =>
          cases assump_3
          case intro assump_128 assump_129 =>
            cases assump_128
            case intro assump_130 assump_131 =>
              cases assump_129
              case intro assump_136 assump_137 =>
                cases assump_136
                case intro assump_138 assump_139 =>
                  cases assump_138
                  case intro assump_140 assump_141 =>
                    cases assump_139
                    case intro assump_146 assump_147 =>
                      cases assump_137
                      case intro assump_152 assump_153 =>
                        cases assump_152
                        case intro assump_154 assump_155 =>
                          apply False.elim assump_155


variable (p4 p2 p0 p3 p6 p7 : Prop)
theorem file32_51648 : ((((((p7 ∨ p3) → False) → ((p0 ∨ p4) → (p4 ∨ p4))) → False) ∧ ((((p6 ∧ p7) ∨ (False → p4)) ∨ ((p6 ∨ True) ∧ (p2 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p6 ∧ p7) ∨ (False → p4)) ∨ ((p6 ∨ True) ∧ (p2 → p7))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p2 p3 p7 p1 p6 p4 : Prop)
theorem file32_52165 : ((((((False ∧ p1) → False) → ((False ∧ p2) ∧ (p7 ∨ p6))) → (((p2 → False) ∧ (p3 → p6)) ∧ ((p4 ∧ p1) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_58 : ((((False ∧ p1) → False) → ((False ∧ p2) ∧ (p7 ∨ p6))) → (((p2 → False) ∧ (p3 → p6)) ∧ ((p4 ∧ p1) ∨ (p3 → False)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    have assump_59 : ((False ∧ p1) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_11 := assump_5 assump_59
    let assump_17 := And.left assump_11
    let assump_18 := And.left assump_17
    apply False.elim assump_18
    intro assump_22
    have assump_60 : ((False ∧ p1) → False) := by
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
    let assump_27 := assump_5 assump_60
    let assump_33 := And.left assump_27
    let assump_34 := And.left assump_33
    apply False.elim assump_34
    apply Or.inr
    intro assump_40
    have assump_61 : ((False ∧ p1) → False) := by
      intro assump_45
      cases assump_45
      case intro assump_46 assump_47 =>
        apply False.elim assump_46
    let assump_44 := assump_5 assump_61
    let assump_50 := And.left assump_44
    let assump_51 := And.left assump_50
    apply False.elim assump_51
  let assump_4 := assump_1 assump_58
  apply False.elim assump_4


variable (p0 p4 p5 p7 p1 p3 : Prop)
theorem file32_53685 : (((((False → False) ∨ (p4 → False)) → False) ∧ (((p3 ∨ p4) → False) ∧ ((p7 ∨ p1) → (p3 → p0)))) → ((((p5 ∨ p3) → (p0 ∨ p4)) ∨ ((p5 → False) → (p0 → False))) ∨ (((p1 → p1) ∨ (True ∧ p5)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        have assump_35 : ((False → False) ∨ (p4 → False)) := by
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_2 assump_35
        apply False.elim assump_20
      case inr assump_14 =>
        have assump_36 : (p3 ∨ p4) := by
          apply Or.inl
          exact assump_14
        let assump_31 := assump_6 assump_36
        apply False.elim assump_31


variable (p5 p6 p2 p7 p4 : Prop)
theorem file32_54604 : (((((p2 → False) → (False → False)) → False) → (((p6 ∨ p5) ∧ (False → p6)) ∧ ((p7 → False) → False))) ∨ ((((p7 → p4) → (False → False)) ∧ ((p6 ∨ p2) → (p4 → False))) ∨ (((p7 → p6) → False) ∧ ((False ∧ True) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_28 : ((p2 → False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4
  intro assump_12
  apply False.elim assump_12
  intro assump_15
  have assump_29 : ((p2 → False) → (False → False)) := by
    intro assump_21
    intro assump_22
    apply False.elim assump_22
  let assump_20 := assump_1 assump_29
  apply False.elim assump_20


variable (p3 p7 p6 p1 p2 p4 : Prop)
theorem file32_55416 : ((((((p4 → p7) ∨ (True → False)) ∨ ((p2 ∨ p2) ∨ (False → p3))) → False) ∧ ((((p6 ∧ p3) ∨ (True ∧ p1)) ∨ ((p1 → False) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p6 ∧ p3) ∨ (True ∧ p1)) ∨ ((p1 → False) ∨ (p3 → False))) := by
      apply Or.inr
      apply Or.inl
      intro assump_9
      have assump_21 : (((p6 ∧ p3) ∨ (True ∧ p1)) ∨ ((p1 → False) ∨ (p3 → False))) := by
        apply Or.inl
        apply Or.inr
        apply And.intro
        apply True.intro
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p6 p7 p1 p3 p4 p0 p5 p2 : Prop)
theorem file32_56203 : (((((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) → False) → ((((p6 → p0) ∨ (p3 ∨ p4)) ∧ ((p1 → False) ∨ (p7 ∧ p1))) → (((p6 ∨ p0) → (p6 ∨ p6)) → ((p6 ∧ p3) → (p7 → False))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_6
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_21
        case inl assump_26 =>
          have assump_176 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
            apply And.intro
            intro assump_33
            apply Or.inl
            exact assump_13
            intro assump_36
            intro assump_37
            have assump_177 : True := by
              apply True.intro
            let assump_42 := assump_36 assump_177
            apply False.elim assump_42
          let assump_32 := assump_5 assump_176
          apply False.elim assump_32
        case inr assump_27 =>
          cases assump_27
          case intro assump_49 assump_50 =>
            have assump_178 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
              apply And.intro
              intro assump_58
              apply Or.inl
              exact assump_13
              intro assump_61
              intro assump_62
              have assump_179 : True := by
                apply True.intro
              let assump_67 := assump_61 assump_179
              apply False.elim assump_67
            let assump_57 := assump_5 assump_178
            apply False.elim assump_57
      case inr assump_23 =>
        cases assump_23
        case inl assump_74 =>
          cases assump_21
          case inl assump_78 =>
            have assump_180 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
              apply And.intro
              intro assump_85
              apply Or.inl
              exact assump_74
              intro assump_88
              intro assump_89
              have assump_181 : True := by
                apply True.intro
              let assump_94 := assump_88 assump_181
              apply False.elim assump_94
            let assump_84 := assump_5 assump_180
            apply False.elim assump_84
          case inr assump_79 =>
            cases assump_79
            case intro assump_101 assump_102 =>
              have assump_182 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
                apply And.intro
                intro assump_110
                apply Or.inl
                exact assump_74
                intro assump_113
                intro assump_114
                have assump_183 : True := by
                  apply True.intro
                let assump_119 := assump_113 assump_183
                apply False.elim assump_119
              let assump_109 := assump_5 assump_182
              apply False.elim assump_109
        case inr assump_75 =>
          cases assump_21
          case inl assump_128 =>
            have assump_184 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
              apply And.intro
              intro assump_135
              apply Or.inl
              exact assump_13
              intro assump_138
              intro assump_139
              have assump_185 : True := by
                apply True.intro
              let assump_144 := assump_138 assump_185
              apply False.elim assump_144
            let assump_134 := assump_5 assump_184
            apply False.elim assump_134
          case inr assump_129 =>
            cases assump_129
            case intro assump_151 assump_152 =>
              have assump_186 : (((p2 → False) → (p3 ∨ p4)) ∧ ((True → False) → (p1 → p5))) := by
                apply And.intro
                intro assump_160
                apply Or.inl
                exact assump_13
                intro assump_163
                intro assump_164
                have assump_187 : True := by
                  apply True.intro
                let assump_169 := assump_163 assump_187
                apply False.elim assump_169
              let assump_159 := assump_5 assump_186
              apply False.elim assump_159


variable (p0 p7 p5 p6 p4 : Prop)
theorem file32_60530 : (((((p7 ∨ True) ∨ (p0 → False)) → ((p6 ∧ p4) ∨ (p6 ∧ p5))) ∧ (((p4 → True) ∨ (p5 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p4 → True) ∨ (p5 → False)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p0 p7 p3 p4 p1 p5 p6 : Prop)
theorem file32_60965 : (((((False ∨ False) → (p5 ∨ p3)) ∨ ((p0 → False) → (p4 ∧ p5))) ∨ (((p7 ∧ False) ∨ (p6 ∨ p7)) ∨ ((p7 → False) ∧ (p3 → p3)))) ∨ ((((p6 ∧ p4) → (p1 → p0)) → ((p3 → p3) ∨ (p5 ∨ p1))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply False.elim assump_6
  case inr assump_7 =>
    apply False.elim assump_7


variable (p6 p1 p0 : Prop)
theorem file32_61396 : ((((((p0 → False) → False) → ((p6 → p1) ∧ (p0 → False))) → (((p1 ∧ p0) ∨ (p0 → False)) ∨ ((p6 ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 → False) → False) → ((p6 → p1) ∧ (p0 → False))) → (((p1 ∧ p0) ∨ (p0 → False)) ∨ ((p6 ∨ p1) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_30 : ((p0 → False) → False) := by
      intro assump_13
      have assump_31 : p0 := by
        exact assump_8
      let assump_16 := assump_13 assump_31
      apply False.elim assump_16
    let assump_12 := assump_5 assump_30
    let assump_20 := And.right assump_12
    have assump_32 : p0 := by
      exact assump_8
    let assump_22 := assump_20 assump_32
    apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p3 p7 p6 p4 p5 p0 p1 : Prop)
theorem file32_62292 : (((((False → False) ∨ (p1 → False)) ∨ ((False ∧ p0) → False)) ∨ (((p1 → False) ∧ (True → True)) → ((p4 → False) → False))) ∨ ((((p5 → False) ∧ (p1 ∨ p2)) ∧ ((p1 ∧ False) ∨ (p7 → False))) → (((p5 ∨ p6) → False) ∨ ((p0 ∧ p3) ∧ (p0 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p5 p3 p0 p1 p7 p2 : Prop)
theorem file32_62702 : (((((True ∨ p0) → (p5 → False)) → ((p7 → False) → (p0 → False))) → False) → ((((p2 ∨ p0) → (p0 ∨ True)) ∨ ((p3 ∧ p7) → False)) ∨ (((p7 → p1) ∧ (p2 ∨ p3)) → ((p7 → p0) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    apply Or.inl
    exact assump_6


variable (p6 p4 p5 : Prop)
theorem file32_63139 : (((((True ∧ p5) ∨ (p5 → False)) → False) ∧ (((p5 → False) → (p4 ∨ True)) → False)) → ((((True ∧ True) → False) → ((False → p6) ∨ (p4 ∨ True))) → False)) := by
  intro assump_18
  intro assump_19
  cases assump_18
  case intro assump_22 assump_23 =>
    have assump_35 : ((p5 → False) → (p4 ∨ True)) := by
      intro assump_29
      apply Or.inr
      apply True.intro
    let assump_28 := assump_23 assump_35
    apply False.elim assump_28


variable (p2 p6 p3 p0 p5 p7 p4 p1 : Prop)
theorem file32_63646 : (((((True ∨ p4) → (p3 → p2)) ∨ ((p5 → False) ∨ (p0 ∨ p0))) → False) → ((((p7 → p6) ∨ (p3 → p7)) ∧ ((p5 → p6) ∧ (p7 → False))) → (((p4 → False) → (False → False)) ∨ ((p6 ∧ p1) → (p0 ∨ p2))))) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_21
        intro assump_22
        apply False.elim assump_22
    case inr assump_10 =>
      cases assump_8
      case intro assump_27 assump_28 =>
        apply Or.inl
        intro assump_35
        intro assump_36
        apply False.elim assump_36


variable (p1 p7 p6 p4 p5 p0 p2 : Prop)
theorem file32_64391 : ((((((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) → False) ∧ ((((False → p5) → (p6 → False)) ∧ ((p6 ∧ p2) → (p4 → False))) ∧ (((p4 ∨ p4) ∨ (p5 ∨ p7)) ∨ ((p0 → p2) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              have assump_142 : (((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) := by
                intro assump_30
                intro assump_31
                cases assump_30
                case intro assump_34 assump_35 =>
                  cases assump_34
                  case intro assump_36 assump_37 =>
                    apply False.elim assump_36
              let assump_29 := assump_2 assump_142
              apply False.elim assump_29
            case inr assump_19 =>
              have assump_143 : (((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) := by
                intro assump_53
                intro assump_54
                cases assump_53
                case intro assump_57 assump_58 =>
                  cases assump_57
                  case intro assump_59 assump_60 =>
                    apply False.elim assump_59
              let assump_52 := assump_2 assump_143
              apply False.elim assump_52
          case inr assump_17 =>
            cases assump_17
            case inl assump_66 =>
              have assump_144 : (((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) := by
                intro assump_78
                intro assump_79
                cases assump_78
                case intro assump_82 assump_83 =>
                  cases assump_82
                  case intro assump_84 assump_85 =>
                    apply False.elim assump_84
              let assump_77 := assump_2 assump_144
              apply False.elim assump_77
            case inr assump_67 =>
              have assump_145 : (((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) := by
                intro assump_101
                intro assump_102
                cases assump_101
                case intro assump_105 assump_106 =>
                  cases assump_105
                  case intro assump_107 assump_108 =>
                    apply False.elim assump_107
              let assump_100 := assump_2 assump_145
              apply False.elim assump_100
        case inr assump_15 =>
          cases assump_15
          case intro assump_114 assump_115 =>
            have assump_146 : (((False ∧ p0) ∧ (p2 ∨ p4)) → ((p1 → False) → False)) := by
              intro assump_129
              intro assump_130
              cases assump_129
              case intro assump_133 assump_134 =>
                cases assump_133
                case intro assump_135 assump_136 =>
                  apply False.elim assump_135
            let assump_128 := assump_2 assump_146
            apply False.elim assump_128


variable (p7 p3 p6 p4 p5 p0 : Prop)
theorem file32_67591 : (((((p5 ∧ p3) → False) → ((p4 ∨ p6) → False)) → (((p6 → False) ∧ (True ∧ p5)) → ((False → p0) ∨ (False ∧ p7)))) → ((((False ∧ False) ∧ (True ∧ False)) → ((p6 ∧ p3) ∧ (p3 → False))) ∨ (((p5 ∧ p7) → False) ∨ ((p0 ∧ p3) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  cases assump_4
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  intro assump_17
  cases assump_4
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      apply False.elim assump_22


variable (p3 p6 p1 p7 p0 p4 p5 : Prop)
theorem file32_68418 : ((((((p4 ∧ p1) ∧ (p3 ∧ p5)) ∧ ((p6 ∧ p7) → (p3 → p1))) ∧ (((p0 ∧ True) ∨ (p7 → False)) → False)) ∧ ((((p3 ∨ p6) ∧ (p7 → True)) → False) ∧ (((p5 → p3) ∨ (p5 → p4)) ∧ ((p4 → False) ∧ (p0 ∧ p4))))) → False) := by
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
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_26 assump_27 =>
                cases assump_27
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_31
                    case intro assump_36 assump_37 =>
                      cases assump_37
                      case intro assump_40 assump_41 =>
                        have assump_70 : p4 := by
                          exact assump_41
                        let assump_48 := assump_36 assump_70
                        apply False.elim assump_48
                  case inr assump_33 =>
                    cases assump_31
                    case intro assump_54 assump_55 =>
                      cases assump_55
                      case intro assump_58 assump_59 =>
                        have assump_71 : p4 := by
                          exact assump_59
                        let assump_66 := assump_54 assump_71
                        apply False.elim assump_66


variable (p3 p7 p4 p6 p0 p1 : Prop)
theorem file32_70124 : ((((((p4 → False) → (p4 → False)) → False) → False) ∧ ((((p6 ∨ p3) ∨ (p1 ∧ p0)) → ((True ∧ True) → False)) ∧ (((p4 ∧ p3) ∧ (p7 → False)) ∧ ((p0 ∧ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_33 : ((p6 ∨ p3) ∨ (p1 ∧ p0)) := by
              apply Or.inl
              apply Or.inr
              exact assump_15
            let assump_28 := assump_6 assump_33
            have assump_34 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_29 := assump_28 assump_34
            apply False.elim assump_29


variable (p2 p0 p7 p4 p5 p3 p6 : Prop)
theorem file32_71104 : (((((p2 ∨ p2) → (p7 ∨ True)) → False) ∧ (((p3 → False) ∨ (p7 → False)) ∨ ((p3 ∧ p4) ∧ (True ∧ True)))) → ((((p0 → False) → (p6 ∧ p3)) ∨ ((p5 ∨ p5) → False)) ∧ (((True → p6) → (p7 → True)) → ((p5 → False) ∨ (p3 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        apply And.intro
        have assump_187 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            apply Or.inr
            apply True.intro
          case inr assump_20 =>
            apply Or.inr
            apply True.intro
        let assump_17 := assump_2 assump_187
        apply False.elim assump_17
        have assump_188 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_33
          cases assump_33
          case inl assump_34 =>
            apply Or.inr
            apply True.intro
          case inr assump_35 =>
            apply Or.inr
            apply True.intro
        let assump_32 := assump_2 assump_188
        apply False.elim assump_32
      case inr assump_9 =>
        apply Or.inl
        intro assump_45
        apply And.intro
        have assump_189 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_51
          cases assump_51
          case inl assump_52 =>
            apply Or.inr
            apply True.intro
          case inr assump_53 =>
            apply Or.inr
            apply True.intro
        let assump_50 := assump_2 assump_189
        apply False.elim assump_50
        have assump_190 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_66
          cases assump_66
          case inl assump_67 =>
            apply Or.inr
            apply True.intro
          case inr assump_68 =>
            apply Or.inr
            apply True.intro
        let assump_65 := assump_2 assump_190
        apply False.elim assump_65
    case inr assump_7 =>
      cases assump_7
      case intro assump_76 assump_77 =>
        cases assump_76
        case intro assump_78 assump_79 =>
          cases assump_77
          case intro assump_84 assump_85 =>
            apply Or.inl
            intro assump_90
            apply And.intro
            have assump_191 : ((p2 ∨ p2) → (p7 ∨ True)) := by
              intro assump_97
              cases assump_97
              case inl assump_98 =>
                apply Or.inr
                apply True.intro
              case inr assump_99 =>
                apply Or.inr
                apply True.intro
            let assump_96 := assump_2 assump_191
            apply False.elim assump_96
            exact assump_78
  intro assump_109
  cases assump_1
  case intro assump_112 assump_113 =>
    cases assump_113
    case inl assump_116 =>
      cases assump_116
      case inl assump_118 =>
        apply Or.inl
        intro assump_122
        have assump_192 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_128
          cases assump_128
          case inl assump_129 =>
            apply Or.inr
            apply True.intro
          case inr assump_130 =>
            apply Or.inr
            apply True.intro
        let assump_127 := assump_112 assump_192
        apply False.elim assump_127
      case inr assump_119 =>
        apply Or.inl
        intro assump_140
        have assump_193 : ((p2 ∨ p2) → (p7 ∨ True)) := by
          intro assump_146
          cases assump_146
          case inl assump_147 =>
            apply Or.inr
            apply True.intro
          case inr assump_148 =>
            apply Or.inr
            apply True.intro
        let assump_145 := assump_112 assump_193
        apply False.elim assump_145
    case inr assump_117 =>
      cases assump_117
      case intro assump_156 assump_157 =>
        cases assump_156
        case intro assump_158 assump_159 =>
          cases assump_157
          case intro assump_164 assump_165 =>
            apply Or.inl
            intro assump_170
            have assump_194 : ((p2 ∨ p2) → (p7 ∨ True)) := by
              intro assump_177
              cases assump_177
              case inl assump_178 =>
                apply Or.inr
                apply True.intro
              case inr assump_179 =>
                apply Or.inr
                apply True.intro
            let assump_176 := assump_112 assump_194
            apply False.elim assump_176


variable (p4 p6 p7 p0 p1 : Prop)
theorem file32_75655 : (((((p7 ∨ True) ∨ (True → p6)) ∨ ((p4 ∨ p0) → (False → p1))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p7 ∨ True) ∨ (True → p6)) ∨ ((p4 ∨ p0) → (False → p1))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p0 p4 p2 p6 p7 p5 : Prop)
theorem file32_76039 : ((((((True ∨ p2) ∨ (p5 ∧ p7)) → False) → False) ∧ ((((p6 ∧ p4) ∨ (p0 ∨ p1)) → False) ∧ (((p6 → True) ∨ (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : ((p6 → True) ∨ (p5 → False)) := by
        apply Or.inl
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p5 p2 p0 p1 p4 p6 : Prop)
theorem file32_76568 : (((((False → p6) ∨ (p0 ∧ p2)) → False) → False) ∨ ((((True ∧ p4) ∧ (p1 → False)) → False) ∧ (((p5 ∨ p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → p6) ∨ (p0 ∧ p2)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p4 p5 p1 p7 p6 : Prop)
theorem file32_76973 : (((((p5 ∨ p1) → (p3 → p7)) → False) ∧ (((p6 ∨ p6) → (p7 → p4)) → ((p3 → False) → (p4 → False)))) → ((((False → p4) → False) → False) ∨ (((p1 → False) ∨ (p4 → False)) ∨ ((p6 → False) → False)))) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    apply Or.inl
    intro assump_21
    have assump_31 : (False → p4) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_21 assump_31
    apply False.elim assump_24


variable (p0 p3 p1 p6 p7 p2 p4 : Prop)
theorem file32_77512 : ((((((p3 ∧ p7) → (p2 ∧ True)) ∨ ((p2 → p1) ∨ (p4 ∧ p1))) → (((p0 ∨ p6) ∧ (p3 → False)) ∨ ((False → False) → (True ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 ∧ p7) → (p2 ∧ True)) ∨ ((p2 → p1) ∨ (p4 ∧ p1))) → (((p0 ∨ p6) ∧ (p3 → False)) ∨ ((False → False) → (True ∨ p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_13 =>
        apply Or.inr
        intro assump_17
        apply Or.inl
        apply True.intro
      case inr assump_14 =>
        cases assump_14
        case intro assump_20 assump_21 =>
          apply Or.inr
          intro assump_26
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p0 p7 p1 p3 p4 p5 p6 p2 : Prop)
theorem file32_78457 : (((((p1 ∧ p6) ∨ (p0 ∧ p7)) ∨ ((p0 ∨ p4) → (p7 ∧ p7))) → False) → ((((p2 ∧ p3) → False) ∧ ((p5 → p7) ∨ (False ∧ p5))) → (((p7 ∧ p0) → (True → p4)) ∨ ((p2 → p1) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      intro assump_14
      cases assump_13
      case intro assump_17 assump_18 =>
        have assump_33 : (((p1 ∧ p6) ∨ (p0 ∧ p7)) ∨ ((p0 ∨ p4) → (p7 ∧ p7))) := by
          apply Or.inl
          apply Or.inr
          apply And.intro
          exact assump_18
          exact assump_17
        let assump_25 := assump_1 assump_33
        apply False.elim assump_25
    case inr assump_8 =>
      cases assump_8
      case intro assump_29 assump_30 =>
        apply False.elim assump_29


variable (p1 p6 p2 p7 p0 p4 p5 p3 : Prop)
theorem file32_79361 : (((((p1 → False) → False) ∧ ((p3 ∨ p5) → (p3 ∨ p4))) → (((p1 ∧ p2) → (p1 ∧ p7)) → ((p0 ∧ p3) ∨ (True ∨ p5)))) ∨ ((((False ∧ p7) → (p3 ∧ p0)) → ((p6 ∧ p1) ∧ (False → False))) → (((p5 → False) ∨ (p7 ∨ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p3 p1 p4 p2 p6 : Prop)
theorem file32_79794 : ((((((False ∨ p4) → (False → p6)) ∨ ((p3 ∧ p2) ∧ (True ∧ True))) ∨ (((p1 ∨ p6) → (False ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False ∨ p4) → (False → p6)) ∨ ((p3 ∧ p2) ∧ (True ∧ True))) ∨ (((p1 ∨ p6) → (False ∧ p2)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p0 p3 p5 p6 p4 : Prop)
theorem file32_80295 : ((((((False ∨ p0) ∧ (p3 → p6)) → False) ∧ (((p6 ∧ False) → False) → False)) ∨ ((((p2 → False) → False) → ((p2 → p5) → (False → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_32 : ((p6 ∧ False) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
      let assump_10 := assump_5 assump_32
      apply False.elim assump_10
  case inr assump_3 =>
    have assump_33 : (((p2 → False) → False) → ((p2 → p5) → (False → p4))) := by
      intro assump_24
      intro assump_25
      intro assump_26
      apply False.elim assump_26
    let assump_23 := assump_3 assump_33
    apply False.elim assump_23


variable (p2 p3 p7 p1 p6 : Prop)
theorem file32_81150 : (((((p2 ∧ p7) → (p2 ∨ p7)) → False) → (((False ∨ p1) ∧ (p2 ∨ p7)) → False)) ∨ ((((p3 ∧ p6) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      cases assump_4
      case inl assump_11 =>
        have assump_43 : ((p2 ∧ p7) → (p2 ∨ p7)) := by
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply Or.inl
            exact assump_19
        let assump_17 := assump_1 assump_43
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_44 : ((p2 ∧ p7) → (p2 ∨ p7)) := by
          intro assump_33
          cases assump_33
          case intro assump_34 assump_35 =>
            apply Or.inl
            exact assump_34
        let assump_32 := assump_1 assump_44
        apply False.elim assump_32


variable (p7 p3 p2 p4 p6 p1 : Prop)
theorem file32_82179 : (((((p4 ∧ p6) → (p7 ∨ p7)) ∧ ((True → False) ∧ (p1 ∧ True))) → False) ∨ ((((p3 → False) ∧ (True → p6)) ∨ ((True ∧ True) ∧ (p3 ∧ p2))) → (((p2 → p7) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_21 : True := by
          apply True.intro
        let assump_17 := assump_6 assump_21
        apply False.elim assump_17


variable (p3 p6 p2 p1 p7 p5 p0 : Prop)
theorem file32_82757 : ((((((True ∧ p3) ∧ (True → False)) ∧ ((p3 → p1) → (p2 → False))) ∨ (((True → False) ∧ (p6 → p0)) ∨ ((p3 → p7) → False))) ∧ ((((p0 → p7) ∨ (p0 → False)) → ((p1 ∧ False) → (p5 ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            have assump_90 : (((p0 → p7) ∨ (p0 → False)) → ((p1 ∧ False) → (p5 ∧ p3))) := by
              intro assump_23
              intro assump_24
              apply And.intro
              cases assump_24
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
              cases assump_24
              case intro assump_31 assump_32 =>
                apply False.elim assump_32
            let assump_22 := assump_3 assump_90
            apply False.elim assump_22
    case inr assump_5 =>
      cases assump_5
      case inl assump_40 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          have assump_91 : (((p0 → p7) ∨ (p0 → False)) → ((p1 ∧ False) → (p5 ∧ p3))) := by
            intro assump_51
            intro assump_52
            apply And.intro
            cases assump_52
            case intro assump_53 assump_54 =>
              apply False.elim assump_54
            cases assump_52
            case intro assump_59 assump_60 =>
              apply False.elim assump_60
          let assump_50 := assump_3 assump_91
          apply False.elim assump_50
      case inr assump_41 =>
        have assump_92 : (((p0 → p7) ∨ (p0 → False)) → ((p1 ∧ False) → (p5 ∧ p3))) := by
          intro assump_73
          intro assump_74
          apply And.intro
          cases assump_74
          case intro assump_75 assump_76 =>
            apply False.elim assump_76
          cases assump_74
          case intro assump_81 assump_82 =>
            apply False.elim assump_82
        let assump_72 := assump_3 assump_92
        apply False.elim assump_72


variable (p5 p6 : Prop)
theorem file32_84947 : ((((((True ∧ p6) → (p5 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∧ p6) → (p5 → True)) → False) → False) := by
    intro assump_5
    have assump_18 : ((True ∧ p6) → (p5 → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_5 assump_18
    apply False.elim assump_8
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p2 p6 p1 p3 : Prop)
theorem file32_85442 : ((((((p5 ∧ p1) → (True → p2)) ∧ ((False ∨ False) ∧ (p6 ∧ p1))) → (((p6 ∨ p1) → False) ∧ ((p1 → p1) ∨ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p5 ∧ p1) → (True → p2)) ∧ ((False ∨ False) ∧ (p6 ∧ p1))) → (((p6 ∨ p1) → False) ∧ ((p1 → p1) ∨ (p3 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply False.elim assump_18
    case inr assump_8 =>
      cases assump_5
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          cases assump_29
          case inl assump_31 =>
            apply False.elim assump_31
          case inr assump_32 =>
            apply False.elim assump_32
    cases assump_5
    case intro assump_37 assump_38 =>
      cases assump_38
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          apply False.elim assump_43
        case inr assump_44 =>
          apply False.elim assump_44
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p2 p4 p0 p3 : Prop)
theorem file32_86853 : ((((((False ∨ p3) ∨ (p2 → False)) ∧ ((p4 → p0) ∧ (True ∧ False))) → (((p2 ∨ True) ∨ (p4 → False)) → False)) → False) → False) := by
  intro assump_5
  have assump_120 : ((((False ∨ p3) ∨ (p2 → False)) ∧ ((p4 → p0) ∧ (True ∧ False))) → (((p2 ∨ True) ∨ (p4 → False)) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_9
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case inl assump_21 =>
              apply False.elim assump_21
            case inr assump_22 =>
              cases assump_18
              case intro assump_27 assump_28 =>
                cases assump_28
                case intro assump_31 assump_32 =>
                  apply False.elim assump_32
          case inr assump_20 =>
            cases assump_18
            case intro assump_39 assump_40 =>
              cases assump_40
              case intro assump_43 assump_44 =>
                apply False.elim assump_44
      case inr assump_14 =>
        cases assump_9
        case intro assump_51 assump_52 =>
          cases assump_51
          case inl assump_53 =>
            cases assump_53
            case inl assump_55 =>
              apply False.elim assump_55
            case inr assump_56 =>
              cases assump_52
              case intro assump_61 assump_62 =>
                cases assump_62
                case intro assump_65 assump_66 =>
                  apply False.elim assump_66
          case inr assump_54 =>
            cases assump_52
            case intro assump_73 assump_74 =>
              cases assump_74
              case intro assump_77 assump_78 =>
                apply False.elim assump_78
    case inr assump_12 =>
      cases assump_9
      case intro assump_85 assump_86 =>
        cases assump_85
        case inl assump_87 =>
          cases assump_87
          case inl assump_89 =>
            apply False.elim assump_89
          case inr assump_90 =>
            cases assump_86
            case intro assump_95 assump_96 =>
              cases assump_96
              case intro assump_99 assump_100 =>
                apply False.elim assump_100
        case inr assump_88 =>
          cases assump_86
          case intro assump_107 assump_108 =>
            cases assump_108
            case intro assump_111 assump_112 =>
              apply False.elim assump_112
  let assump_8 := assump_5 assump_120
  apply False.elim assump_8


variable (p7 p6 p0 p4 p2 p3 : Prop)
theorem file32_89495 : ((((((p7 ∨ p4) → (p4 ∨ p7)) → False) ∧ (((p2 ∧ True) → False) ∧ ((p3 ∧ True) → False))) ∧ ((((p2 ∧ p4) ∧ (p7 ∧ p4)) ∨ ((p6 ∧ p7) ∨ (p0 ∧ p0))) → False)) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        have assump_45 : ((p7 ∨ p4) → (p4 ∨ p7)) := by
          intro assump_35
          cases assump_35
          case inl assump_36 =>
            apply Or.inr
            exact assump_36
          case inr assump_37 =>
            apply Or.inl
            exact assump_37
        let assump_34 := assump_19 assump_45
        apply False.elim assump_34


variable (p2 p3 p1 : Prop)
theorem file32_90263 : ((((((True ∨ p1) → (p3 → False)) ∨ ((p2 ∧ False) → False)) → (((False → p2) → False) → False)) → False) → False) := by
  intro assump_5
  have assump_39 : ((((True ∨ p1) → (p3 → False)) ∨ ((p2 ∧ False) → False)) → (((False → p2) → False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_9
    case inl assump_13 =>
      have assump_40 : (False → p2) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_10 assump_40
      apply False.elim assump_19
    case inr assump_14 =>
      have assump_41 : (False → p2) := by
        intro assump_30
        apply False.elim assump_30
      let assump_29 := assump_10 assump_41
      apply False.elim assump_29
  let assump_8 := assump_5 assump_39
  apply False.elim assump_8


variable (p6 p5 p7 p4 p2 p1 p0 : Prop)
theorem file32_91109 : (((((p5 → False) ∧ (p1 ∧ p4)) ∧ ((p4 → False) → (p6 → False))) → (((False → False) ∨ (p0 ∨ True)) ∨ ((p5 → False) ∨ (p1 ∧ p6)))) ∨ ((((False → p2) ∧ (True → False)) → ((p7 ∨ True) ∧ (p6 → p6))) → (((p5 → False) → (p5 → p0)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        apply False.elim assump_16


variable (p4 p2 p5 p0 : Prop)
theorem file32_91702 : ((((((True ∨ p2) → False) → ((p5 → False) → (True ∨ p2))) → False) ∨ ((((True → p0) → False) → ((p0 ∨ p5) ∨ (p4 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_26 : (((True ∨ p2) → False) → ((p5 → False) → (True ∨ p2))) := by
      intro assump_7
      intro assump_8
      apply Or.inl
      apply True.intro
    let assump_6 := assump_2 assump_26
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_27 : (((True → p0) → False) → ((p0 ∨ p5) ∨ (p4 → True))) := by
      intro assump_19
      apply Or.inr
      intro assump_22
      apply True.intro
    let assump_18 := assump_3 assump_27
    apply False.elim assump_18


variable (p7 p5 p0 p3 p6 p1 p4 : Prop)
theorem file32_92463 : (((((True → False) ∧ (p7 ∨ p6)) ∨ ((p0 → p6) → False)) → (((p3 ∧ p1) ∨ (p5 ∨ p6)) → ((True → False) ∨ (True ∨ p7)))) → ((((False ∧ p5) ∧ (False → False)) ∧ ((True → False) ∨ (p3 ∨ p6))) → (((p7 ∧ True) ∨ (False ∨ p6)) ∨ ((p4 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p7 p0 p6 p2 p3 p4 p1 : Prop)
theorem file32_93008 : (((((p6 → False) → (p0 → p0)) → False) → (((p3 → False) → (p0 ∨ p6)) ∧ ((p4 ∨ False) → (p3 → False)))) ∨ ((((p1 ∨ p2) ∨ (p6 ∨ p4)) → ((True → p4) → (p4 → False))) → (((False ∧ p7) ∨ (p0 → p7)) → ((p0 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_39 : ((p6 → False) → (p0 → p0)) := by
    intro assump_8
    intro assump_9
    exact assump_9
  let assump_7 := assump_1 assump_39
  apply False.elim assump_7
  intro assump_17
  intro assump_18
  cases assump_17
  case inl assump_21 =>
    have assump_40 : ((p6 → False) → (p0 → p0)) := by
      intro assump_28
      intro assump_29
      exact assump_29
    let assump_27 := assump_1 assump_40
    apply False.elim assump_27
  case inr assump_22 =>
    apply False.elim assump_22


variable (p4 p1 p5 p7 p0 p2 p3 : Prop)
theorem file32_93863 : (((((p2 → p2) → (True ∨ p1)) ∨ ((p1 ∨ p2) → False)) ∨ (((p4 → False) ∧ (p3 ∧ False)) → False)) ∨ ((((p0 ∨ p3) ∨ (p5 ∧ p1)) → False) ∧ (((False → False) ∧ (p4 ∨ p5)) ∨ ((False ∨ p1) → (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply True.intro


variable (p1 p4 p7 p3 p0 p2 p6 p5 : Prop)
theorem file32_94231 : (((((False ∧ p3) → False) ∨ ((p7 → False) → (False ∧ True))) ∧ (((p4 → False) ∨ (False ∨ p1)) ∧ ((True ∨ p2) → (p7 → p0)))) → ((((p5 ∧ p5) ∨ (p6 → False)) → ((p7 → p7) ∧ (False → p1))) ∨ (((True → False) ∨ (p4 ∧ p2)) ∨ ((p4 ∧ p3) ∧ (p1 ∨ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_16
          apply And.intro
          intro assump_17
          cases assump_16
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              exact assump_17
          case inr assump_21 =>
            exact assump_17
          intro assump_30
          apply False.elim assump_30
        case inr assump_11 =>
          cases assump_11
          case inl assump_33 =>
            apply False.elim assump_33
          case inr assump_34 =>
            apply Or.inl
            intro assump_41
            apply And.intro
            intro assump_42
            cases assump_41
            case inl assump_45 =>
              cases assump_45
              case intro assump_47 assump_48 =>
                exact assump_42
            case inr assump_46 =>
              exact assump_42
            intro assump_55
            apply False.elim assump_55
    case inr assump_5 =>
      cases assump_3
      case intro assump_60 assump_61 =>
        cases assump_60
        case inl assump_62 =>
          apply Or.inl
          intro assump_68
          apply And.intro
          intro assump_69
          cases assump_68
          case inl assump_72 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              exact assump_69
          case inr assump_73 =>
            exact assump_69
          intro assump_82
          apply False.elim assump_82
        case inr assump_63 =>
          cases assump_63
          case inl assump_85 =>
            apply False.elim assump_85
          case inr assump_86 =>
            apply Or.inl
            intro assump_93
            apply And.intro
            intro assump_94
            cases assump_93
            case inl assump_97 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                exact assump_94
            case inr assump_98 =>
              exact assump_94
            intro assump_107
            apply False.elim assump_107


variable (p7 p4 p1 p2 : Prop)
theorem file32_96818 : (((((False → p7) ∨ (p2 → False)) → False) ∧ (((p1 ∨ p7) → (p2 → p4)) ∧ ((p4 → p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : (p4 → p4) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p5 p2 p7 p0 p4 p3 : Prop)
theorem file32_97271 : (((((p0 → False) → False) ∨ ((p4 ∨ True) → False)) → False) → ((((p3 → False) ∨ (p4 → True)) ∧ ((p2 ∨ p3) ∧ (p5 ∧ p0))) → (((p3 ∧ p2) → False) ∨ ((p7 → p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case intro assump_15 assump_16 =>
            apply Or.inl
            intro assump_23
            cases assump_23
            case intro assump_24 assump_25 =>
              have assump_139 : (((p0 → False) → False) ∨ ((p4 ∨ True) → False)) := by
                apply Or.inl
                intro assump_33
                have assump_140 : p0 := by
                  exact assump_16
                let assump_36 := assump_33 assump_140
                apply False.elim assump_36
              let assump_32 := assump_1 assump_139
              apply False.elim assump_32
        case inr assump_12 =>
          cases assump_10
          case intro assump_45 assump_46 =>
            apply Or.inl
            intro assump_53
            cases assump_53
            case intro assump_54 assump_55 =>
              have assump_141 : (((p0 → False) → False) ∨ ((p4 ∨ True) → False)) := by
                apply Or.inl
                intro assump_63
                have assump_142 : p0 := by
                  exact assump_46
                let assump_66 := assump_63 assump_142
                apply False.elim assump_66
              let assump_62 := assump_1 assump_141
              apply False.elim assump_62
    case inr assump_6 =>
      cases assump_4
      case intro assump_75 assump_76 =>
        cases assump_75
        case inl assump_77 =>
          cases assump_76
          case intro assump_81 assump_82 =>
            apply Or.inl
            intro assump_89
            cases assump_89
            case intro assump_90 assump_91 =>
              have assump_143 : (((p0 → False) → False) ∨ ((p4 ∨ True) → False)) := by
                apply Or.inl
                intro assump_99
                have assump_144 : p0 := by
                  exact assump_82
                let assump_102 := assump_99 assump_144
                apply False.elim assump_102
              let assump_98 := assump_1 assump_143
              apply False.elim assump_98
        case inr assump_78 =>
          cases assump_76
          case intro assump_111 assump_112 =>
            apply Or.inl
            intro assump_119
            cases assump_119
            case intro assump_120 assump_121 =>
              have assump_145 : (((p0 → False) → False) ∨ ((p4 ∨ True) → False)) := by
                apply Or.inl
                intro assump_129
                have assump_146 : p0 := by
                  exact assump_112
                let assump_132 := assump_129 assump_146
                apply False.elim assump_132
              let assump_128 := assump_1 assump_145
              apply False.elim assump_128


variable (p7 p3 p4 p2 p5 p6 : Prop)
theorem file32_100406 : ((((((p5 ∧ True) ∧ (p5 → False)) ∧ ((p3 ∨ p6) → False)) → (((p7 → p7) ∧ (p5 → p7)) ∧ ((p2 → False) ∨ (False ∧ p4)))) → ((((False → p5) ∨ (p5 ∨ p7)) → False) ∧ (((p6 ∧ p3) → (p2 → False)) → ((False → p5) → (True → False))))) → False) := by
  intro assump_1
  have assump_76 : ((((p5 ∧ True) ∧ (p5 → False)) ∧ ((p3 ∨ p6) → False)) → (((p7 → p7) ∧ (p5 → p7)) ∧ ((p2 → False) ∨ (False ∧ p4)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          exact assump_6
    intro assump_23
    cases assump_5
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          have assump_77 : p5 := by
            exact assump_30
          let assump_41 := assump_29 assump_77
          apply False.elim assump_41
    cases assump_5
    case intro assump_45 assump_46 =>
      cases assump_45
      case intro assump_47 assump_48 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          apply Or.inl
          intro assump_59
          have assump_78 : p5 := by
            exact assump_49
          let assump_64 := assump_48 assump_78
          apply False.elim assump_64
  let assump_4 := assump_1 assump_76
  let assump_68 := And.left assump_4
  have assump_79 : ((False → p5) ∨ (p5 ∨ p7)) := by
    apply Or.inl
    intro assump_70
    apply False.elim assump_70
  let assump_69 := assump_68 assump_79
  apply False.elim assump_69


variable (p6 p4 p3 p2 p7 p5 p1 p0 : Prop)
theorem file32_102151 : (((((p7 ∧ p5) → (p0 ∨ p7)) ∨ ((p0 ∧ p1) ∧ (p2 → p3))) ∨ (((p1 ∧ p7) ∧ (p6 → False)) ∨ ((p0 ∨ p5) ∨ (p2 ∧ p4)))) ∨ ((((p5 ∧ p7) → False) ∧ ((p7 ∧ True) ∧ (p3 → False))) ∧ (((p7 ∨ p4) ∧ (p4 ∧ False)) ∧ ((p4 ∨ True) ∧ (True ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    exact assump_2


variable (p6 p0 : Prop)
theorem file32_102585 : (((((True ∨ True) ∨ (p0 → p0)) ∨ ((p0 → False) → (p6 ∧ p6))) → False) → ((((p6 → False) ∨ (p6 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((True ∨ True) ∨ (p0 → p0)) ∨ ((p0 → False) → (p6 ∧ p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p4 p3 p5 p1 p6 p2 p0 : Prop)
theorem file32_103032 : (((((p3 ∨ p4) ∨ (p6 ∨ p4)) → ((True ∧ p4) ∨ (True → p5))) ∨ (((p1 ∧ p1) ∨ (p2 ∨ p3)) → ((False ∨ False) → (p0 → False)))) → ((((False → p6) ∨ (False ∨ False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    have assump_27 : ((False → p6) ∨ (False ∨ False)) := by
      apply Or.inl
      intro assump_11
      apply False.elim assump_11
    let assump_10 := assump_2 assump_27
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_28 : ((False → p6) ∨ (False ∨ False)) := by
      apply Or.inl
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_2 assump_28
    apply False.elim assump_20


variable (p4 p5 p3 p7 p2 p0 : Prop)
theorem file32_103783 : (((((p0 ∧ p2) → False) → False) ∧ (((p0 ∧ True) ∨ (p3 ∨ p7)) → False)) → ((((p5 → False) → (p5 → False)) → False) ∧ (((p7 ∧ p2) ∨ (p0 ∨ p2)) ∧ ((False → p5) → (p4 ∨ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_80 : ((p0 ∧ p2) → False) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        have assump_81 : ((p0 ∧ True) ∨ (p3 ∨ p7)) := by
          apply Or.inl
          apply And.intro
          exact assump_14
          apply True.intro
        let assump_22 := assump_6 assump_81
        apply False.elim assump_22
    let assump_12 := assump_5 assump_80
    apply False.elim assump_12
  apply And.intro
  cases assump_1
  case intro assump_29 assump_30 =>
    have assump_82 : ((p0 ∧ p2) → False) := by
      intro assump_37
      cases assump_37
      case intro assump_38 assump_39 =>
        have assump_83 : ((p0 ∧ True) ∨ (p3 ∨ p7)) := by
          apply Or.inl
          apply And.intro
          exact assump_38
          apply True.intro
        let assump_46 := assump_30 assump_83
        apply False.elim assump_46
    let assump_36 := assump_29 assump_82
    apply False.elim assump_36
  intro assump_53
  cases assump_1
  case intro assump_56 assump_57 =>
    have assump_84 : ((p0 ∧ p2) → False) := by
      intro assump_64
      cases assump_64
      case intro assump_65 assump_66 =>
        have assump_85 : ((p0 ∧ True) ∨ (p3 ∨ p7)) := by
          apply Or.inl
          apply And.intro
          exact assump_65
          apply True.intro
        let assump_73 := assump_57 assump_85
        apply False.elim assump_73
    let assump_63 := assump_56 assump_84
    apply False.elim assump_63


variable (p1 p7 p3 p2 : Prop)
theorem file32_105585 : ((((((p2 → p2) → False) → False) ∨ (((p2 → p3) → False) → ((p3 → p3) → (p1 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → p2) → False) → False) ∨ (((p2 → p3) → False) → ((p3 → p3) → (p1 ∧ p7)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (p2 → p2) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p4 p6 : Prop)
theorem file32_106120 : ((((((p6 ∧ p3) ∨ (p6 → False)) → ((True ∧ True) → (False → False))) ∨ (((p7 ∨ False) ∨ (p4 → p3)) → ((p7 → p3) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p6 ∧ p3) ∨ (p6 → False)) → ((True ∧ True) → (False → False))) ∨ (((p7 ∨ False) ∨ (p4 → p3)) → ((p7 → p3) ∨ (True → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p0 p1 p2 p7 p6 p5 p4 : Prop)
theorem file32_106681 : (((((p5 → False) ∧ (p7 ∨ p4)) → ((p0 → p0) ∨ (p7 ∧ True))) ∨ (((p6 → False) → (p6 ∧ p2)) → False)) → ((((True → False) → False) ∧ ((p0 → False) → False)) → (((p2 ∧ p4) → (p6 ∨ p2)) → ((p4 → p4) ∨ (p3 ∧ p1))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case intro assump_10 assump_11 =>
    cases assump_5
    case inl assump_16 =>
      apply Or.inl
      intro assump_20
      exact assump_20
    case inr assump_17 =>
      apply Or.inl
      intro assump_25
      exact assump_25


variable (p7 p3 p4 p1 p0 p6 p5 : Prop)
theorem file32_107261 : ((((((p4 ∨ p3) ∧ (p4 → p1)) ∧ ((p0 ∨ p4) → False)) → (((p1 → False) ∨ (p4 ∨ True)) → False)) ∧ ((((p5 ∨ p1) ∨ (p4 ∨ p6)) → False) ∧ (((p7 → p6) ∨ (p4 → False)) ∧ ((p5 ∨ p6) ∨ (p0 ∧ p6))))) → False) := by
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
              have assump_84 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inl
                apply Or.inl
                exact assump_18
              let assump_24 := assump_6 assump_84
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_85 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inr
                apply Or.inr
                exact assump_19
              let assump_32 := assump_6 assump_85
              apply False.elim assump_32
          case inr assump_17 =>
            cases assump_17
            case intro assump_36 assump_37 =>
              have assump_86 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inr
                apply Or.inr
                exact assump_37
              let assump_45 := assump_6 assump_86
              apply False.elim assump_45
        case inr assump_13 =>
          cases assump_11
          case inl assump_51 =>
            cases assump_51
            case inl assump_53 =>
              have assump_87 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inl
                apply Or.inl
                exact assump_53
              let assump_59 := assump_6 assump_87
              apply False.elim assump_59
            case inr assump_54 =>
              have assump_88 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inr
                apply Or.inr
                exact assump_54
              let assump_67 := assump_6 assump_88
              apply False.elim assump_67
          case inr assump_52 =>
            cases assump_52
            case intro assump_71 assump_72 =>
              have assump_89 : ((p5 ∨ p1) ∨ (p4 ∨ p6)) := by
                apply Or.inr
                apply Or.inr
                exact assump_72
              let assump_80 := assump_6 assump_89
              apply False.elim assump_80


variable (p5 p2 p7 p6 p1 p0 p3 : Prop)
theorem file32_109768 : ((((((p7 → False) → False) ∧ ((p6 → False) → False)) ∧ (((p1 ∨ p1) → (p1 → False)) → ((p6 → False) → (p0 ∨ p5)))) ∧ ((((p2 → p3) ∧ (p1 ∨ p3)) → ((True → True) ∨ (True ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_33 : (((p2 → p3) ∧ (p1 ∨ p3)) → ((True → True) ∨ (True ∧ False))) := by
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              apply Or.inl
              intro assump_26
              apply True.intro
            case inr assump_23 =>
              apply Or.inl
              intro assump_29
              apply True.intro
        let assump_16 := assump_3 assump_33
        apply False.elim assump_16


variable (p6 p7 p1 p4 p2 : Prop)
theorem file32_110749 : (((((True ∨ p2) → False) → False) → False) → ((((p2 ∧ p6) → False) ∧ ((p4 ∨ p2) ∧ (p1 → False))) → (((True → False) → (p4 → p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        have assump_48 : (((True ∨ p2) → False) → False) := by
          intro assump_21
          have assump_49 : (True ∨ p2) := by
            apply Or.inl
            apply True.intro
          let assump_24 := assump_21 assump_49
          apply False.elim assump_24
        let assump_20 := assump_1 assump_48
        apply False.elim assump_20
      case inr assump_13 =>
        have assump_50 : (((True ∨ p2) → False) → False) := by
          intro assump_38
          have assump_51 : (True ∨ p2) := by
            apply Or.inl
            apply True.intro
          let assump_41 := assump_38 assump_51
          apply False.elim assump_41
        let assump_37 := assump_1 assump_50
        apply False.elim assump_37


variable (p7 p0 p6 p2 p1 p3 p4 p5 : Prop)
theorem file32_111900 : (((((p0 → p0) → (True → False)) ∧ ((p2 ∨ p2) ∧ (p7 → p7))) → (((p4 ∨ True) → False) → ((p6 ∨ p1) ∧ (p5 → False)))) ∨ ((((False → p6) → (p3 ∧ True)) ∨ ((p4 ∧ False) ∨ (p3 ∨ p3))) ∨ (((p2 ∨ p3) ∨ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  apply And.intro
  cases assump_12
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        have assump_93 : (p0 → p0) := by
          intro assump_31
          exact assump_31
        let assump_30 := assump_16 assump_93
        have assump_94 : True := by
          apply True.intro
        let assump_34 := assump_30 assump_94
        apply False.elim assump_34
      case inr assump_23 =>
        have assump_95 : (p0 → p0) := by
          intro assump_45
          exact assump_45
        let assump_44 := assump_16 assump_95
        have assump_96 : True := by
          apply True.intro
        let assump_48 := assump_44 assump_96
        apply False.elim assump_48
  intro assump_52
  cases assump_12
  case intro assump_57 assump_58 =>
    cases assump_58
    case intro assump_61 assump_62 =>
      cases assump_61
      case inl assump_63 =>
        have assump_97 : (p0 → p0) := by
          intro assump_72
          exact assump_72
        let assump_71 := assump_57 assump_97
        have assump_98 : True := by
          apply True.intro
        let assump_75 := assump_71 assump_98
        apply False.elim assump_75
      case inr assump_64 =>
        have assump_99 : (p0 → p0) := by
          intro assump_86
          exact assump_86
        let assump_85 := assump_57 assump_99
        have assump_100 : True := by
          apply True.intro
        let assump_89 := assump_85 assump_100
        apply False.elim assump_89


variable (p6 p2 p5 p4 p3 p0 : Prop)
theorem file32_113778 : (((((False → True) → False) → ((p0 ∧ p6) ∧ (p3 ∨ True))) → False) → ((((p6 ∨ True) → False) ∨ ((p4 ∨ p6) → (p4 ∧ p5))) ∧ (((False ∧ p4) ∨ (p2 → p3)) → False))) := by
  intro assump_9
  apply And.intro
  apply Or.inl
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_89 : (((False → True) → False) → ((p0 ∧ p6) ∧ (p3 ∨ True))) := by
      intro assump_19
      apply And.intro
      apply And.intro
      have assump_90 : (False → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_19 assump_90
      apply False.elim assump_22
      exact assump_13
      apply Or.inr
      apply True.intro
    let assump_18 := assump_9 assump_89
    apply False.elim assump_18
  case inr assump_14 =>
    have assump_91 : (((False → True) → False) → ((p0 ∧ p6) ∧ (p3 ∨ True))) := by
      intro assump_37
      apply And.intro
      apply And.intro
      have assump_92 : (False → True) := by
        intro assump_41
        apply True.intro
      let assump_40 := assump_37 assump_92
      apply False.elim assump_40
      have assump_93 : (False → True) := by
        intro assump_48
        apply True.intro
      let assump_47 := assump_37 assump_93
      apply False.elim assump_47
      apply Or.inr
      apply True.intro
    let assump_36 := assump_9 assump_91
    apply False.elim assump_36
  intro assump_57
  cases assump_57
  case inl assump_58 =>
    cases assump_58
    case intro assump_60 assump_61 =>
      apply False.elim assump_60
  case inr assump_59 =>
    have assump_94 : (((False → True) → False) → ((p0 ∧ p6) ∧ (p3 ∨ True))) := by
      intro assump_69
      apply And.intro
      apply And.intro
      have assump_95 : (False → True) := by
        intro assump_73
        apply True.intro
      let assump_72 := assump_69 assump_95
      apply False.elim assump_72
      have assump_96 : (False → True) := by
        intro assump_80
        apply True.intro
      let assump_79 := assump_69 assump_96
      apply False.elim assump_79
      apply Or.inr
      apply True.intro
    let assump_68 := assump_9 assump_94
    apply False.elim assump_68


