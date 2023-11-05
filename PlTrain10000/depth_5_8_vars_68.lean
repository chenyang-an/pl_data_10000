variable (p6 p1 p3 p5 : Prop)
theorem file68_38 : ((((((p5 ∧ False) ∧ (p6 ∨ p6)) → False) → (((True ∨ p3) ∧ (p6 → False)) → ((p6 ∨ p1) → (True → p1)))) → False) → False) := by
  intro assump_18
  have assump_79 : ((((p5 ∧ False) ∧ (p6 ∨ p6)) → False) → (((True ∨ p3) ∧ (p6 → False)) → ((p6 ∨ p1) → (True → p1)))) := by
    intro assump_22
    intro assump_23
    intro assump_24
    intro assump_25
    cases assump_24
    case inl assump_28 =>
      cases assump_23
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          have assump_80 : p6 := by
            exact assump_28
          let assump_43 := assump_33 assump_80
          apply False.elim assump_43
        case inr assump_35 =>
          have assump_81 : p6 := by
            exact assump_28
          let assump_54 := assump_33 assump_81
          apply False.elim assump_54
    case inr assump_29 =>
      cases assump_23
      case intro assump_60 assump_61 =>
        cases assump_60
        case inl assump_62 =>
          exact assump_29
        case inr assump_63 =>
          exact assump_29
  let assump_21 := assump_18 assump_79
  apply False.elim assump_21


variable (p3 p4 p1 p2 p5 p6 p7 : Prop)
theorem file68_1230 : (((((False → False) ∨ (p1 ∨ p5)) ∨ ((p1 ∧ False) ∨ (p6 ∧ p4))) → (((True → False) ∧ (p3 ∧ False)) → ((p4 → False) ∧ (False ∧ p6)))) ∨ ((((p2 ∧ p7) → False) ∨ ((p4 ∨ p4) ∨ (p4 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  apply And.intro
  cases assump_2
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      apply False.elim assump_21
  cases assump_2
  case intro assump_26 assump_27 =>
    cases assump_27
    case intro assump_30 assump_31 =>
      apply False.elim assump_31


variable (p2 p7 p3 p5 p1 p4 p6 p0 : Prop)
theorem file68_2029 : (((((True ∧ p7) → (False → False)) ∨ ((p0 ∨ p4) → False)) ∨ (((p4 ∨ p6) ∧ (p2 ∧ p7)) ∧ ((p2 ∨ p3) → False))) ∨ ((((p3 → p1) ∧ (p7 ∧ False)) → ((p1 → p6) → (p2 ∨ p5))) ∧ (((p0 → False) → (p5 → p5)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p6 p7 p4 p1 p0 : Prop)
theorem file68_2407 : ((((((p1 ∨ p7) ∧ (False → False)) ∨ ((False ∧ p1) → (True ∨ True))) → (((p0 ∧ True) → (p4 → p7)) → ((p4 → p6) → (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 ∨ p7) ∧ (False → False)) ∨ ((False ∧ p1) → (True ∨ True))) → (((p0 ∧ True) → (p4 → p7)) → ((p4 → p6) → (True ∧ True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p1 p2 p0 : Prop)
theorem file68_2970 : ((((((p2 ∨ True) ∧ (p6 ∨ p1)) ∧ ((p7 → p0) ∨ (p6 → False))) → (((p7 ∧ p6) → (True → False)) → ((False → False) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∨ True) ∧ (p6 ∨ p1)) ∧ ((p7 → p0) ∨ (p6 → False))) → (((p7 ∧ p6) → (True → False)) → ((False → False) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p5 p7 p4 p3 p6 p2 p0 : Prop)
theorem file68_3535 : (((((p4 ∨ p5) → False) ∨ ((p0 → p1) ∧ (p3 ∧ False))) ∨ (((p0 → False) ∧ (p4 → False)) → False)) → ((((True → False) ∨ (p0 ∨ p3)) ∧ ((p3 ∨ p6) ∧ (p3 ∧ p2))) → (((p5 ∨ True) ∨ (True → False)) ∧ ((p7 → False) → (p5 → p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
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
            cases assump_1
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
              case inr assump_24 =>
                cases assump_24
                case intro assump_27 assump_28 =>
                  cases assump_28
                  case intro assump_31 assump_32 =>
                    apply False.elim assump_32
            case inr assump_22 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
        case inr assump_12 =>
          cases assump_10
          case intro assump_41 assump_42 =>
            cases assump_1
            case inl assump_47 =>
              cases assump_47
              case inl assump_49 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
              case inr assump_50 =>
                cases assump_50
                case intro assump_53 assump_54 =>
                  cases assump_54
                  case intro assump_57 assump_58 =>
                    apply False.elim assump_58
            case inr assump_48 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
    case inr assump_6 =>
      cases assump_6
      case inl assump_65 =>
        cases assump_4
        case intro assump_69 assump_70 =>
          cases assump_69
          case inl assump_71 =>
            cases assump_70
            case intro assump_75 assump_76 =>
              cases assump_1
              case inl assump_81 =>
                cases assump_81
                case inl assump_83 =>
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                case inr assump_84 =>
                  cases assump_84
                  case intro assump_87 assump_88 =>
                    cases assump_88
                    case intro assump_91 assump_92 =>
                      apply False.elim assump_92
              case inr assump_82 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
          case inr assump_72 =>
            cases assump_70
            case intro assump_101 assump_102 =>
              cases assump_1
              case inl assump_107 =>
                cases assump_107
                case inl assump_109 =>
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                case inr assump_110 =>
                  cases assump_110
                  case intro assump_113 assump_114 =>
                    cases assump_114
                    case intro assump_117 assump_118 =>
                      apply False.elim assump_118
              case inr assump_108 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
      case inr assump_66 =>
        cases assump_4
        case intro assump_127 assump_128 =>
          cases assump_127
          case inl assump_129 =>
            cases assump_128
            case intro assump_133 assump_134 =>
              cases assump_1
              case inl assump_139 =>
                cases assump_139
                case inl assump_141 =>
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                case inr assump_142 =>
                  cases assump_142
                  case intro assump_145 assump_146 =>
                    cases assump_146
                    case intro assump_149 assump_150 =>
                      apply False.elim assump_150
              case inr assump_140 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
          case inr assump_130 =>
            cases assump_128
            case intro assump_159 assump_160 =>
              cases assump_1
              case inl assump_165 =>
                cases assump_165
                case inl assump_167 =>
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                case inr assump_168 =>
                  cases assump_168
                  case intro assump_171 assump_172 =>
                    cases assump_172
                    case intro assump_175 assump_176 =>
                      apply False.elim assump_176
              case inr assump_166 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
  intro assump_183
  intro assump_184
  cases assump_2
  case intro assump_189 assump_190 =>
    cases assump_189
    case inl assump_191 =>
      cases assump_190
      case intro assump_195 assump_196 =>
        cases assump_195
        case inl assump_197 =>
          cases assump_196
          case intro assump_201 assump_202 =>
            cases assump_1
            case inl assump_207 =>
              cases assump_207
              case inl assump_209 =>
                exact assump_184
              case inr assump_210 =>
                cases assump_210
                case intro assump_213 assump_214 =>
                  cases assump_214
                  case intro assump_217 assump_218 =>
                    apply False.elim assump_218
            case inr assump_208 =>
              exact assump_184
        case inr assump_198 =>
          cases assump_196
          case intro assump_227 assump_228 =>
            cases assump_1
            case inl assump_233 =>
              cases assump_233
              case inl assump_235 =>
                exact assump_184
              case inr assump_236 =>
                cases assump_236
                case intro assump_239 assump_240 =>
                  cases assump_240
                  case intro assump_243 assump_244 =>
                    apply False.elim assump_244
            case inr assump_234 =>
              exact assump_184
    case inr assump_192 =>
      cases assump_192
      case inl assump_251 =>
        cases assump_190
        case intro assump_255 assump_256 =>
          cases assump_255
          case inl assump_257 =>
            cases assump_256
            case intro assump_261 assump_262 =>
              cases assump_1
              case inl assump_267 =>
                cases assump_267
                case inl assump_269 =>
                  exact assump_184
                case inr assump_270 =>
                  cases assump_270
                  case intro assump_273 assump_274 =>
                    cases assump_274
                    case intro assump_277 assump_278 =>
                      apply False.elim assump_278
              case inr assump_268 =>
                exact assump_184
          case inr assump_258 =>
            cases assump_256
            case intro assump_287 assump_288 =>
              cases assump_1
              case inl assump_293 =>
                cases assump_293
                case inl assump_295 =>
                  exact assump_184
                case inr assump_296 =>
                  cases assump_296
                  case intro assump_299 assump_300 =>
                    cases assump_300
                    case intro assump_303 assump_304 =>
                      apply False.elim assump_304
              case inr assump_294 =>
                exact assump_184
      case inr assump_252 =>
        cases assump_190
        case intro assump_313 assump_314 =>
          cases assump_313
          case inl assump_315 =>
            cases assump_314
            case intro assump_319 assump_320 =>
              cases assump_1
              case inl assump_325 =>
                cases assump_325
                case inl assump_327 =>
                  exact assump_184
                case inr assump_328 =>
                  cases assump_328
                  case intro assump_331 assump_332 =>
                    cases assump_332
                    case intro assump_335 assump_336 =>
                      apply False.elim assump_336
              case inr assump_326 =>
                exact assump_184
          case inr assump_316 =>
            cases assump_314
            case intro assump_345 assump_346 =>
              cases assump_1
              case inl assump_351 =>
                cases assump_351
                case inl assump_353 =>
                  exact assump_184
                case inr assump_354 =>
                  cases assump_354
                  case intro assump_357 assump_358 =>
                    cases assump_358
                    case intro assump_361 assump_362 =>
                      apply False.elim assump_362
              case inr assump_352 =>
                exact assump_184


variable (p1 p5 p2 p4 p7 : Prop)
theorem file68_12882 : ((((((True → False) → (p5 → False)) → ((False ∨ True) ∨ (p2 ∧ p4))) ∨ (((p7 → p1) → False) ∧ ((p7 → False) ∨ (p7 → False)))) → False) → False) := by
  intro assump_14
  have assump_24 : ((((True → False) → (p5 → False)) → ((False ∨ True) ∨ (p2 ∧ p4))) ∨ (((p7 → p1) → False) ∧ ((p7 → False) ∨ (p7 → False)))) := by
    apply Or.inl
    intro assump_18
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_17 := assump_14 assump_24
  apply False.elim assump_17


variable (p6 p1 p7 p2 p4 p3 : Prop)
theorem file68_13417 : (((((True → p2) → (p3 ∨ p3)) → ((p6 → False) → (True ∨ p7))) → False) → ((((p3 ∨ p3) → (p6 → False)) → False) → (((p4 → False) → (False → False)) ∨ ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p4 p5 p2 p1 p3 p7 : Prop)
theorem file68_13768 : ((((((p7 → False) ∨ (False → True)) → ((p3 → False) → False)) ∨ (((p2 ∨ p3) ∨ (p7 ∧ p2)) → False)) ∧ ((((p4 ∧ p1) ∨ (False → p4)) ∨ ((p5 ∨ False) ∧ (True → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (((p4 ∧ p1) ∨ (False → p4)) ∨ ((p5 ∨ False) ∧ (True → True))) := by
        apply Or.inl
        apply Or.inr
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (((p4 ∧ p1) ∨ (False → p4)) ∨ ((p5 ∨ False) ∧ (True → True))) := by
        apply Or.inl
        apply Or.inr
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p1 p6 p7 p5 p4 p0 p3 p2 : Prop)
theorem file68_14694 : ((((((p2 → p4) → (p6 ∨ False)) ∨ ((p1 ∧ p5) → False)) → False) ∧ ((((p6 ∧ p2) ∨ (p0 ∨ p3)) → ((p4 → False) ∧ (p0 ∨ p7))) ∧ (((p5 → p3) → (p2 ∧ True)) ∧ ((p7 ∨ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_20 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p6 p0 p3 p5 p7 p2 p1 : Prop)
theorem file68_15306 : (((((p0 → p0) ∨ (p3 ∨ p5)) → False) → (((p6 ∨ p6) ∧ (True ∧ True)) ∨ ((False → True) → False))) ∨ ((((p2 ∨ False) → False) ∨ ((False → p7) → (p0 ∧ p0))) ∨ (((p7 → False) ∨ (p7 ∧ p1)) → ((p2 → False) ∧ (False ∧ True))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_15 : ((p0 → p0) ∨ (p3 ∨ p5)) := by
    apply Or.inl
    intro assump_9
    exact assump_9
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p4 p5 p1 p3 p7 : Prop)
theorem file68_15822 : (((((p5 → p5) → False) → ((p7 → False) → (p7 ∧ p3))) → False) → ((((p1 → False) ∧ (p7 → False)) ∨ ((p3 ∨ p4) → (True ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_73 : (((p5 → p5) → False) → ((p7 → False) → (p7 ∧ p3))) := by
        intro assump_14
        intro assump_15
        apply And.intro
        have assump_74 : (p5 → p5) := by
          intro assump_21
          exact assump_21
        let assump_20 := assump_14 assump_74
        apply False.elim assump_20
        have assump_75 : (p5 → p5) := by
          intro assump_32
          exact assump_32
        let assump_31 := assump_14 assump_75
        apply False.elim assump_31
      let assump_13 := assump_1 assump_73
      apply False.elim assump_13
  case inr assump_4 =>
    have assump_76 : (((p5 → p5) → False) → ((p7 → False) → (p7 ∧ p3))) := by
      intro assump_46
      intro assump_47
      apply And.intro
      have assump_77 : (p5 → p5) := by
        intro assump_53
        exact assump_53
      let assump_52 := assump_46 assump_77
      apply False.elim assump_52
      have assump_78 : (p5 → p5) := by
        intro assump_64
        exact assump_64
      let assump_63 := assump_46 assump_78
      apply False.elim assump_63
    let assump_45 := assump_1 assump_76
    apply False.elim assump_45


variable (p1 p5 p3 p4 p7 p2 : Prop)
theorem file68_17289 : (((((p1 → False) → (p7 ∧ False)) → ((p1 → p1) → (p2 ∨ p3))) → False) → ((((True → False) → (p2 → p3)) ∨ ((p4 ∧ p5) ∨ (p5 → False))) → (((p3 ∧ p5) ∧ (p4 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_14 =>
        have assump_64 : (((p1 → False) → (p7 ∧ False)) → ((p1 → p1) → (p2 ∨ p3))) := by
          intro assump_21
          intro assump_22
          apply Or.inr
          exact assump_6
        let assump_20 := assump_1 assump_64
        apply False.elim assump_20
      case inr assump_15 =>
        cases assump_15
        case inl assump_30 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            have assump_65 : (((p1 → False) → (p7 ∧ False)) → ((p1 → p1) → (p2 ∨ p3))) := by
              intro assump_41
              intro assump_42
              apply Or.inr
              exact assump_6
            let assump_40 := assump_1 assump_65
            apply False.elim assump_40
        case inr assump_31 =>
          have assump_66 : (((p1 → False) → (p7 ∧ False)) → ((p1 → p1) → (p2 ∨ p3))) := by
            intro assump_55
            intro assump_56
            apply Or.inr
            exact assump_6
          let assump_54 := assump_1 assump_66
          apply False.elim assump_54


variable (p5 p4 p3 p1 p6 p0 p7 : Prop)
theorem file68_18765 : (((((False ∧ p7) ∧ (p0 ∧ p4)) ∨ ((p1 ∨ p7) ∨ (p1 ∧ False))) → False) → ((((p5 ∨ p5) ∧ (False → p3)) ∧ ((p3 ∨ True) → (True → False))) → (((False → True) → (p3 ∧ p0)) ∧ ((p6 ∨ p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply And.intro
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        have assump_147 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_21 := assump_7 assump_147
        have assump_148 : True := by
          apply True.intro
        let assump_22 := assump_21 assump_148
        apply False.elim assump_22
      case inr assump_11 =>
        have assump_149 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_35 := assump_7 assump_149
        have assump_150 : True := by
          apply True.intro
        let assump_36 := assump_35 assump_150
        apply False.elim assump_36
  cases assump_2
  case intro assump_42 assump_43 =>
    cases assump_42
    case intro assump_44 assump_45 =>
      cases assump_44
      case inl assump_46 =>
        have assump_151 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_57 := assump_43 assump_151
        have assump_152 : True := by
          apply True.intro
        let assump_58 := assump_57 assump_152
        apply False.elim assump_58
      case inr assump_47 =>
        have assump_153 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_71 := assump_43 assump_153
        have assump_154 : True := by
          apply True.intro
        let assump_72 := assump_71 assump_154
        apply False.elim assump_72
  intro assump_76
  cases assump_76
  case inl assump_77 =>
    cases assump_2
    case intro assump_81 assump_82 =>
      cases assump_81
      case intro assump_83 assump_84 =>
        cases assump_83
        case inl assump_85 =>
          have assump_155 : (p3 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_96 := assump_82 assump_155
          have assump_156 : True := by
            apply True.intro
          let assump_97 := assump_96 assump_156
          apply False.elim assump_97
        case inr assump_86 =>
          have assump_157 : (p3 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_110 := assump_82 assump_157
          have assump_158 : True := by
            apply True.intro
          let assump_111 := assump_110 assump_158
          apply False.elim assump_111
  case inr assump_78 =>
    cases assump_2
    case intro assump_117 assump_118 =>
      cases assump_117
      case intro assump_119 assump_120 =>
        cases assump_119
        case inl assump_121 =>
          have assump_159 : (((False ∧ p7) ∧ (p0 ∧ p4)) ∨ ((p1 ∨ p7) ∨ (p1 ∧ False))) := by
            apply Or.inr
            apply Or.inl
            apply Or.inr
            exact assump_78
          let assump_131 := assump_1 assump_159
          apply False.elim assump_131
        case inr assump_122 =>
          have assump_160 : (((False ∧ p7) ∧ (p0 ∧ p4)) ∨ ((p1 ∨ p7) ∨ (p1 ∧ False))) := by
            apply Or.inr
            apply Or.inl
            apply Or.inr
            exact assump_78
          let assump_143 := assump_1 assump_160
          apply False.elim assump_143


variable (p7 p4 : Prop)
theorem file68_22273 : ((((((False → p7) ∧ (True → False)) ∨ ((p4 → p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False → p7) ∧ (True → False)) ∨ ((p4 → p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_31 : True := by
          apply True.intro
        let assump_14 := assump_9 assump_31
        apply False.elim assump_14
    case inr assump_7 =>
      have assump_32 : (p4 → p4) := by
        intro assump_21
        exact assump_21
      let assump_20 := assump_7 assump_32
      apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p5 p3 p0 : Prop)
theorem file68_23040 : ((((((p3 ∧ True) → (p0 → False)) → False) → (((True → False) → False) ∨ ((p3 → False) → (p5 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∧ True) → (p0 → False)) → False) → (((True → False) → False) ∨ ((p3 → False) → (p5 ∧ p5)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p2 p3 p6 p0 p4 p7 p5 : Prop)
theorem file68_23618 : (((((True ∧ True) ∨ (False ∧ p6)) ∨ ((p0 ∨ True) ∧ (p1 ∧ p2))) ∨ (((p7 → False) ∧ (False ∨ False)) ∧ ((p3 → p7) → False))) ∨ ((((p6 → False) ∧ (True → False)) → False) ∨ (((p2 → p4) → False) ∨ ((p3 ∧ p5) → (p3 → p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p7 p3 p2 p0 : Prop)
theorem file68_24014 : ((((((p3 ∨ p0) → (False → False)) → False) → (((True ∨ True) ∨ (True → False)) → ((True ∧ p7) ∧ (p2 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_66 : ((((p3 ∨ p0) → (False → False)) → False) → (((True ∨ True) ∨ (True → False)) → ((True ∧ p7) ∧ (p2 ∨ True)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    apply True.intro
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_67 : ((p3 ∨ p0) → (False → False)) := by
          intro assump_16
          intro assump_17
          apply False.elim assump_17
        let assump_15 := assump_5 assump_67
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_68 : ((p3 ∨ p0) → (False → False)) := by
          intro assump_28
          intro assump_29
          apply False.elim assump_29
        let assump_27 := assump_5 assump_68
        apply False.elim assump_27
    case inr assump_8 =>
      have assump_69 : ((p3 ∨ p0) → (False → False)) := by
        intro assump_40
        intro assump_41
        apply False.elim assump_41
      let assump_39 := assump_5 assump_69
      apply False.elim assump_39
    cases assump_6
    case inl assump_47 =>
      cases assump_47
      case inl assump_49 =>
        apply Or.inr
        apply True.intro
      case inr assump_50 =>
        apply Or.inr
        apply True.intro
    case inr assump_48 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_66
  apply False.elim assump_4


variable (p5 p3 p7 p4 p0 : Prop)
theorem file68_25624 : ((((((p3 ∧ p5) → (p7 → p3)) ∨ ((p7 ∧ p4) ∨ (True ∨ p5))) ∨ (((p0 ∨ p0) → (p5 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∧ p5) → (p7 → p3)) ∨ ((p7 ∧ p4) ∨ (True ∨ p5))) ∨ (((p0 ∨ p0) → (p5 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p2 p4 p3 p0 p6 p1 : Prop)
theorem file68_26159 : (((((p5 ∨ p0) ∨ (p0 → False)) → False) ∧ (((p6 ∧ True) ∧ (p1 → False)) → False)) → ((((p4 ∧ p4) → (p1 → p2)) → ((p3 ∧ False) → (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_25 : ((p5 ∨ p0) ∨ (p0 → False)) := by
      apply Or.inr
      intro assump_13
      have assump_26 : ((p5 ∨ p0) ∨ (p0 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_13
      let assump_18 := assump_5 assump_26
      apply False.elim assump_18
    let assump_12 := assump_5 assump_25
    apply False.elim assump_12


variable (p5 p3 p4 : Prop)
theorem file68_26816 : (((((False → p3) → False) → ((p5 → False) → (p4 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_32 : (((False → p3) → False) → ((p5 → False) → (p4 ∧ p3))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_33 : (False → p3) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_33
    apply False.elim assump_11
    have assump_34 : (False → p3) := by
      intro assump_23
      apply False.elim assump_23
    let assump_22 := assump_5 assump_34
    apply False.elim assump_22
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p2 p0 : Prop)
theorem file68_27495 : (((((True → False) → (p2 → False)) ∨ ((p2 ∨ p0) → False)) → (((False → p0) ∧ (p2 ∨ True)) → False)) → False) := by
  intro assump_1
  have assump_22 : (((True → False) → (p2 → False)) ∨ ((p2 ∨ p0) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_23 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_23
    apply False.elim assump_11
  let assump_4 := assump_1 assump_22
  have assump_24 : ((False → p0) ∧ (p2 ∨ True)) := by
    apply And.intro
    intro assump_16
    apply False.elim assump_16
    apply Or.inr
    apply True.intro
  let assump_15 := assump_4 assump_24
  apply False.elim assump_15


variable (p2 p7 p4 p1 p5 p3 p6 : Prop)
theorem file68_28219 : ((((((p7 ∨ p5) → (p3 ∨ p7)) → False) → False) ∧ ((((p4 ∧ False) → False) ∨ ((p5 → True) ∨ (p2 ∨ p1))) → (((p7 → p4) → (False → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p4 ∧ False) → False) ∨ ((p5 → True) ∨ (p2 ∨ p1))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_24
    have assump_25 : ((p7 → p4) → (False → p6)) := by
      intro assump_17
      intro assump_18
      apply False.elim assump_18
    let assump_16 := assump_8 assump_25
    apply False.elim assump_16


variable (p1 p7 p3 p6 p0 p5 : Prop)
theorem file68_28962 : (((((False → p1) → False) ∧ ((p0 ∨ p6) ∨ (p7 ∧ p3))) ∧ (((p5 → p6) ∨ (p1 → False)) ∨ ((p6 → False) ∨ (p7 → False)))) → ((((p0 ∨ p6) → False) → ((p3 → False) → False)) → (((p3 → False) → False) → False))) := by
  intro assump_32
  intro assump_33
  intro assump_34
  cases assump_32
  case intro assump_39 assump_40 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_42
      case inl assump_45 =>
        cases assump_45
        case inl assump_47 =>
          cases assump_40
          case inl assump_51 =>
            cases assump_51
            case inl assump_53 =>
              have assump_202 : (False → p1) := by
                intro assump_60
                apply False.elim assump_60
              let assump_59 := assump_41 assump_202
              apply False.elim assump_59
            case inr assump_54 =>
              have assump_203 : (False → p1) := by
                intro assump_71
                apply False.elim assump_71
              let assump_70 := assump_41 assump_203
              apply False.elim assump_70
          case inr assump_52 =>
            cases assump_52
            case inl assump_77 =>
              have assump_204 : (False → p1) := by
                intro assump_84
                apply False.elim assump_84
              let assump_83 := assump_41 assump_204
              apply False.elim assump_83
            case inr assump_78 =>
              have assump_205 : (False → p1) := by
                intro assump_95
                apply False.elim assump_95
              let assump_94 := assump_41 assump_205
              apply False.elim assump_94
        case inr assump_48 =>
          cases assump_40
          case inl assump_103 =>
            cases assump_103
            case inl assump_105 =>
              have assump_206 : (False → p1) := by
                intro assump_112
                apply False.elim assump_112
              let assump_111 := assump_41 assump_206
              apply False.elim assump_111
            case inr assump_106 =>
              have assump_207 : (False → p1) := by
                intro assump_123
                apply False.elim assump_123
              let assump_122 := assump_41 assump_207
              apply False.elim assump_122
          case inr assump_104 =>
            cases assump_104
            case inl assump_129 =>
              have assump_208 : p6 := by
                exact assump_48
              let assump_133 := assump_129 assump_208
              apply False.elim assump_133
            case inr assump_130 =>
              have assump_209 : (False → p1) := by
                intro assump_142
                apply False.elim assump_142
              let assump_141 := assump_41 assump_209
              apply False.elim assump_141
      case inr assump_46 =>
        cases assump_46
        case intro assump_148 assump_149 =>
          cases assump_40
          case inl assump_154 =>
            cases assump_154
            case inl assump_156 =>
              have assump_210 : (False → p1) := by
                intro assump_164
                apply False.elim assump_164
              let assump_163 := assump_41 assump_210
              apply False.elim assump_163
            case inr assump_157 =>
              have assump_211 : (False → p1) := by
                intro assump_176
                apply False.elim assump_176
              let assump_175 := assump_41 assump_211
              apply False.elim assump_175
          case inr assump_155 =>
            cases assump_155
            case inl assump_182 =>
              have assump_212 : (False → p1) := by
                intro assump_190
                apply False.elim assump_190
              let assump_189 := assump_41 assump_212
              apply False.elim assump_189
            case inr assump_183 =>
              have assump_213 : p7 := by
                exact assump_148
              let assump_198 := assump_183 assump_213
              apply False.elim assump_198


variable (p7 p3 p5 p6 p2 : Prop)
theorem file68_33040 : ((((((p2 → False) ∨ (False ∧ p5)) → ((p3 ∧ p6) ∧ (p6 → False))) → False) ∧ ((((p2 → p5) ∨ (p7 ∨ p3)) → ((True ∧ p2) ∨ (False → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : (((p2 → p5) ∨ (p7 ∨ p3)) → ((True ∧ p2) ∨ (False → p2))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        intro assump_14
        apply False.elim assump_14
      case inr assump_11 =>
        cases assump_11
        case inl assump_17 =>
          apply Or.inr
          intro assump_21
          apply False.elim assump_21
        case inr assump_18 =>
          apply Or.inr
          intro assump_26
          apply False.elim assump_26
    let assump_8 := assump_3 assump_32
    apply False.elim assump_8


variable (p2 p3 p7 p4 p1 p6 p0 : Prop)
theorem file68_33916 : (((((p6 ∧ False) → (p6 ∧ p3)) ∨ ((p2 → False) ∨ (p1 → False))) ∨ (((p4 ∨ p3) ∧ (p2 ∧ p1)) ∧ ((p3 ∧ p6) → (p0 → False)))) ∨ ((((p4 ∨ p7) → (p6 ∧ p2)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p2 p7 p5 p3 p4 p0 : Prop)
theorem file68_34392 : (((((p0 ∧ p3) ∧ (True → False)) → False) → False) → ((((False ∨ p0) ∨ (p0 ∨ p2)) ∧ ((p0 ∧ p7) ∧ (p4 → False))) ∧ (((p5 → p7) ∨ (False ∧ True)) → False))) := by
  intro assump_18
  apply And.intro
  apply And.intro
  have assump_136 : (((p0 ∧ p3) ∧ (True → False)) → False) := by
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        have assump_137 : True := by
          apply True.intro
        let assump_33 := assump_24 assump_137
        apply False.elim assump_33
  let assump_21 := assump_18 assump_136
  apply False.elim assump_21
  apply And.intro
  apply And.intro
  have assump_138 : (((p0 ∧ p3) ∧ (True → False)) → False) := by
    intro assump_43
    cases assump_43
    case intro assump_44 assump_45 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        have assump_139 : True := by
          apply True.intro
        let assump_54 := assump_45 assump_139
        apply False.elim assump_54
  let assump_42 := assump_18 assump_138
  apply False.elim assump_42
  have assump_140 : (((p0 ∧ p3) ∧ (True → False)) → False) := by
    intro assump_64
    cases assump_64
    case intro assump_65 assump_66 =>
      cases assump_65
      case intro assump_67 assump_68 =>
        have assump_141 : True := by
          apply True.intro
        let assump_75 := assump_66 assump_141
        apply False.elim assump_75
  let assump_63 := assump_18 assump_140
  apply False.elim assump_63
  intro assump_82
  have assump_142 : (((p0 ∧ p3) ∧ (True → False)) → False) := by
    intro assump_88
    cases assump_88
    case intro assump_89 assump_90 =>
      cases assump_89
      case intro assump_91 assump_92 =>
        have assump_143 : True := by
          apply True.intro
        let assump_99 := assump_90 assump_143
        apply False.elim assump_99
  let assump_87 := assump_18 assump_142
  apply False.elim assump_87
  intro assump_106
  cases assump_106
  case inl assump_107 =>
    have assump_144 : (((p0 ∧ p3) ∧ (True → False)) → False) := by
      intro assump_114
      cases assump_114
      case intro assump_115 assump_116 =>
        cases assump_115
        case intro assump_117 assump_118 =>
          have assump_145 : True := by
            apply True.intro
          let assump_125 := assump_116 assump_145
          apply False.elim assump_125
    let assump_113 := assump_18 assump_144
    apply False.elim assump_113
  case inr assump_108 =>
    cases assump_108
    case intro assump_132 assump_133 =>
      apply False.elim assump_132


variable (p6 p1 p3 p4 p2 p5 p7 p0 : Prop)
theorem file68_37040 : (((((True ∧ p4) ∧ (p3 → True)) → ((False ∧ p0) → False)) ∨ (((p6 → False) → (p3 → p4)) ∧ ((p5 ∨ True) → (p4 ∧ p2)))) ∨ ((((p5 ∧ p1) ∧ (p7 ∧ p6)) → ((p3 → False) → False)) ∨ (((False → p6) → (p7 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p5 p0 p6 p3 p1 p4 : Prop)
theorem file68_37466 : ((((((p3 → True) ∧ (p3 → False)) → ((False → p5) → False)) ∨ (((p6 → p1) ∧ (p0 ∧ True)) ∨ ((p4 ∧ p0) → False))) ∧ ((((p1 ∧ p3) → (p3 ∨ p0)) ∨ ((p0 ∨ p5) ∨ (True → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_61 : (((p1 ∧ p3) → (p3 ∨ p0)) ∨ ((p0 ∨ p5) ∨ (True → False))) := by
        apply Or.inl
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply Or.inl
          exact assump_13
      let assump_10 := assump_3 assump_61
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            have assump_62 : (((p1 ∧ p3) → (p3 ∨ p0)) ∨ ((p0 ∨ p5) ∨ (True → False))) := by
              apply Or.inl
              intro assump_36
              cases assump_36
              case intro assump_37 assump_38 =>
                apply Or.inl
                exact assump_38
            let assump_35 := assump_3 assump_62
            apply False.elim assump_35
      case inr assump_22 =>
        have assump_63 : (((p1 ∧ p3) → (p3 ∨ p0)) ∨ ((p0 ∨ p5) ∨ (True → False))) := by
          apply Or.inl
          intro assump_51
          cases assump_51
          case intro assump_52 assump_53 =>
            apply Or.inl
            exact assump_53
        let assump_50 := assump_3 assump_63
        apply False.elim assump_50


variable (p5 p2 p3 p1 p6 p4 p7 : Prop)
theorem file68_39111 : (((((p3 ∧ False) ∧ (p4 ∨ p2)) → ((p6 ∧ p7) → (p6 → False))) ∨ (((p2 → False) → False) ∨ ((True → p4) ∧ (p2 → False)))) ∨ ((((p6 → p1) ∨ (p5 ∨ False)) → ((p2 ∧ True) ∧ (False → False))) ∨ (((p3 ∧ p5) → False) → ((p2 → p2) → (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_7
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21


variable (p1 p6 p4 p5 p2 p0 p3 p7 : Prop)
theorem file68_39711 : (((((False → p0) ∨ (p7 ∧ p2)) → False) → (((False → False) ∨ (False ∧ True)) → ((True ∧ p3) ∨ (p7 → p0)))) ∨ ((((p0 → p3) → (p4 ∧ True)) ∨ ((p4 ∨ p2) ∧ (p5 ∨ p1))) → (((p5 → p7) ∨ (False → p1)) → ((p6 ∧ p4) ∨ (p0 ∧ p1))))) := by
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    apply Or.inr
    intro assump_18
    have assump_33 : ((False → p0) ∨ (p7 ∧ p2)) := by
      apply Or.inl
      intro assump_23
      apply False.elim assump_23
    let assump_22 := assump_10 assump_33
    apply False.elim assump_22
  case inr assump_13 =>
    cases assump_13
    case intro assump_29 assump_30 =>
      apply False.elim assump_29


variable (p1 p2 p0 p3 p6 : Prop)
theorem file68_40442 : (((((p3 ∨ p3) ∨ (p0 ∨ p2)) ∨ ((p1 ∧ p3) → (True ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p3 ∨ p3) ∨ (p0 ∨ p2)) ∨ ((p1 ∧ p3) → (True ∨ p6))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p6 p7 p1 p2 p4 p5 : Prop)
theorem file68_40879 : (((((p2 → True) → False) → ((p6 ∧ p2) ∨ (p2 → p2))) ∨ (((p3 ∨ p3) → (p7 ∨ p1)) → False)) ∨ ((((p3 → False) → False) ∧ ((p3 ∧ p5) ∨ (p3 ∨ p6))) → (((p7 ∨ p4) ∨ (p3 ∨ p4)) ∨ ((p7 → p5) → (False ∨ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  exact assump_4


variable (p6 p1 p7 p0 p4 p2 p3 : Prop)
theorem file68_41246 : (((((p2 → p0) ∨ (False ∨ p4)) → False) ∧ (((p1 ∨ p0) → False) → False)) → ((((p0 → p6) → False) → ((False ∨ p6) → False)) ∨ (((p2 ∧ p3) → False) ∧ ((p2 ∨ p4) → (p7 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      have assump_25 : (p0 → p6) := by
        intro assump_19
        exact assump_11
      let assump_18 := assump_8 assump_25
      apply False.elim assump_18


theorem file68_41839 : ((((((True → False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True → False) → False) → False) → False) := by
    intro assump_5
    have assump_23 : ((True → False) → False) := by
      intro assump_9
      have assump_24 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_24
      apply False.elim assump_12
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p2 p7 p4 p0 : Prop)
theorem file68_42414 : (((((p7 → p2) ∨ (p0 → p4)) → ((p1 ∨ p4) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p7 → p2) ∨ (p0 → p4)) → ((p1 ∨ p4) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p4 p5 p1 p2 p0 : Prop)
theorem file68_42810 : ((((((p7 ∧ False) ∨ (p0 → False)) → ((p7 ∧ True) → (p4 ∧ p4))) → (((False → False) → (True ∧ p2)) ∨ ((p2 → p4) ∨ (p4 → False)))) ∧ ((((p4 → True) ∨ (False ∧ p1)) ∨ ((p5 ∨ p5) ∨ (p2 → True))) ∧ (((p5 → False) → (p2 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_60 : ((p5 → False) → (p2 → True)) := by
            intro assump_17
            intro assump_18
            apply True.intro
          let assump_16 := assump_7 assump_60
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
      case inr assump_9 =>
        cases assump_9
        case inl assump_26 =>
          cases assump_26
          case inl assump_28 =>
            have assump_61 : ((p5 → False) → (p2 → True)) := by
              intro assump_35
              intro assump_36
              apply True.intro
            let assump_34 := assump_7 assump_61
            apply False.elim assump_34
          case inr assump_29 =>
            have assump_62 : ((p5 → False) → (p2 → True)) := by
              intro assump_45
              intro assump_46
              apply True.intro
            let assump_44 := assump_7 assump_62
            apply False.elim assump_44
        case inr assump_27 =>
          have assump_63 : ((p5 → False) → (p2 → True)) := by
            intro assump_55
            intro assump_56
            apply True.intro
          let assump_54 := assump_7 assump_63
          apply False.elim assump_54


variable (p7 p4 p0 p6 : Prop)
theorem file68_44620 : ((((((p7 → False) ∧ (p7 ∧ p4)) ∧ ((False ∨ False) → False)) → (((p0 ∧ p6) ∧ (p6 → p6)) ∧ ((p7 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_92 : ((((p7 → False) ∧ (p7 ∧ p4)) ∧ ((False ∨ False) → False)) → (((p0 ∧ p6) ∧ (p6 → p6)) ∧ ((p7 → p0) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_93 : p7 := by
            exact assump_12
          let assump_23 := assump_8 assump_93
          apply False.elim assump_23
    cases assump_5
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          have assump_94 : p7 := by
            exact assump_33
          let assump_44 := assump_29 assump_94
          apply False.elim assump_44
    intro assump_48
    cases assump_5
    case intro assump_51 assump_52 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        cases assump_54
        case intro assump_57 assump_58 =>
          exact assump_48
    intro assump_65
    cases assump_5
    case intro assump_68 assump_69 =>
      cases assump_68
      case intro assump_70 assump_71 =>
        cases assump_71
        case intro assump_74 assump_75 =>
          have assump_95 : p7 := by
            exact assump_74
          let assump_85 := assump_70 assump_95
          apply False.elim assump_85
  let assump_4 := assump_1 assump_92
  apply False.elim assump_4


variable (p2 p7 p4 p0 p5 p3 : Prop)
theorem file68_46353 : ((((((p2 ∧ p4) → (False → False)) ∨ ((p5 ∧ p0) → (p2 ∨ p0))) ∧ (((p2 → p0) → False) ∧ ((p4 → p2) ∨ (False → False)))) ∧ ((((True ∨ p0) → False) → ((p3 ∧ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_112 : (((True ∨ p0) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_21
              intro assump_22
              cases assump_22
              case intro assump_23 assump_24 =>
                have assump_113 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_31 := assump_21 assump_113
                apply False.elim assump_31
            let assump_20 := assump_3 assump_112
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_114 : (((True ∨ p0) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_43
              intro assump_44
              cases assump_44
              case intro assump_45 assump_46 =>
                have assump_115 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_53 := assump_43 assump_115
                apply False.elim assump_53
            let assump_42 := assump_3 assump_114
            apply False.elim assump_42
      case inr assump_7 =>
        cases assump_5
        case intro assump_62 assump_63 =>
          cases assump_63
          case inl assump_66 =>
            have assump_116 : (((True ∨ p0) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_73
              intro assump_74
              cases assump_74
              case intro assump_75 assump_76 =>
                have assump_117 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_83 := assump_73 assump_117
                apply False.elim assump_83
            let assump_72 := assump_3 assump_116
            apply False.elim assump_72
          case inr assump_67 =>
            have assump_118 : (((True ∨ p0) → False) → ((p3 ∧ p7) → False)) := by
              intro assump_95
              intro assump_96
              cases assump_96
              case intro assump_97 assump_98 =>
                have assump_119 : (True ∨ p0) := by
                  apply Or.inl
                  apply True.intro
                let assump_105 := assump_95 assump_119
                apply False.elim assump_105
            let assump_94 := assump_3 assump_118
            apply False.elim assump_94


variable (p4 p5 p2 : Prop)
theorem file68_49198 : (((((p4 ∨ False) ∨ (True ∨ p5)) → ((False → False) ∧ (False → p2))) ∧ (((False → False) ∨ (False ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (False ∨ True)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p7 p6 p5 p1 : Prop)
theorem file68_49657 : (((((p3 ∧ True) ∧ (True ∨ p7)) ∨ ((False → True) ∨ (p5 ∨ p6))) ∨ (((p6 ∨ p6) → False) → ((False → p1) ∧ (p5 → p1)))) ∨ ((((True ∧ p5) → (False → p1)) → ((p1 → False) → False)) ∨ (((p6 → False) → False) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p5 p2 p1 p3 p6 p0 : Prop)
theorem file68_50049 : ((((((p3 ∧ True) → False) → ((p1 → False) ∨ (p2 → p2))) ∧ (((p2 → False) → False) → False)) ∧ ((((p3 → False) → False) → ((p2 ∨ p5) → False)) ∧ (((p6 ∧ p5) → (p6 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_27 : ((p6 ∧ p5) → (p6 ∨ p0)) := by
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            apply Or.inl
            exact assump_18
        let assump_16 := assump_11 assump_27
        apply False.elim assump_16


variable (p5 p3 p0 p2 p7 p6 : Prop)
theorem file68_50772 : (((((p5 ∨ p7) ∨ (False → False)) → ((p0 ∨ True) ∨ (p3 ∨ p3))) ∨ (((p0 ∧ p3) ∧ (p2 ∨ True)) → False)) ∧ ((((p6 ∨ p5) ∧ (True → p3)) ∧ ((p3 ∧ p0) ∧ (p0 → False))) → (((p6 ∧ p2) → False) → ((False ∨ p6) ∨ (p7 ∨ p7))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        cases assump_17
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply Or.inl
            apply Or.inr
            exact assump_20
      case inr assump_21 =>
        cases assump_17
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            have assump_54 : p0 := by
              exact assump_43
            let assump_50 := assump_41 assump_54
            apply False.elim assump_50


variable (p2 p7 p5 p4 p0 : Prop)
theorem file68_52142 : (((((True → False) → False) ∧ ((False → p5) → False)) → False) ∨ ((((p5 ∧ True) ∧ (p5 ∧ True)) ∧ ((p4 → False) ∧ (p2 → p7))) → (((p0 → True) → (p4 → False)) ∧ ((False ∧ p4) → (p2 → False))))) := by
  apply Or.inl
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    have assump_30 : (False → p5) := by
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_18 assump_30
    apply False.elim assump_23


variable (p4 p5 p2 p7 p3 p0 : Prop)
theorem file68_52654 : ((((((p2 → p2) ∧ (p7 → p0)) → False) → (((p2 → p3) ∧ (p4 → False)) → ((p0 ∧ p4) ∧ (p0 ∧ p5)))) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p0 p7 p2 p3 : Prop)
theorem file68_53267 : (((((False ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p2 ∨ p7) → (p2 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_36 : (((False ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p2 ∨ p7) → (p2 ∧ p3))) := by
    apply Or.inr
    intro assump_5
    apply And.intro
    cases assump_5
    case inl assump_6 =>
      exact assump_6
    case inr assump_7 =>
      have assump_37 : (((False ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p2 ∨ p7) → (p2 ∧ p3))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact assump_7
      let assump_13 := assump_1 assump_37
      apply False.elim assump_13
    cases assump_5
    case inl assump_17 =>
      have assump_38 : (((False ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p2 ∨ p7) → (p2 ∧ p3))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inr
        exact assump_17
      let assump_22 := assump_1 assump_38
      apply False.elim assump_22
    case inr assump_18 =>
      have assump_39 : (((False ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p2 ∨ p7) → (p2 ∧ p3))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact assump_18
      let assump_29 := assump_1 assump_39
      apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p3 p1 p2 p4 p0 p5 : Prop)
theorem file68_54524 : (((((p2 → p1) ∧ (p4 → p2)) → ((p2 → p2) ∨ (p2 ∨ False))) → False) → ((((p3 ∧ p0) → False) ∧ ((p5 → False) ∧ (p5 → p4))) ∧ (((True ∧ True) → (False ∨ p4)) ∨ ((p0 → False) ∧ (p0 ∧ p0))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_86 : (((p2 → p1) ∧ (p4 → p2)) → ((p2 → p2) ∨ (p2 ∨ False))) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_19
        exact assump_19
    let assump_11 := assump_1 assump_86
    apply False.elim assump_11
  apply And.intro
  intro assump_25
  have assump_87 : (((p2 → p1) ∧ (p4 → p2)) → ((p2 → p2) ∨ (p2 ∨ False))) := by
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply Or.inl
      intro assump_38
      exact assump_38
  let assump_30 := assump_1 assump_87
  apply False.elim assump_30
  intro assump_44
  have assump_88 : (((p2 → p1) ∧ (p4 → p2)) → ((p2 → p2) ∨ (p2 ∨ False))) := by
    intro assump_50
    cases assump_50
    case intro assump_51 assump_52 =>
      apply Or.inl
      intro assump_57
      exact assump_57
  let assump_49 := assump_1 assump_88
  apply False.elim assump_49
  apply Or.inl
  intro assump_65
  cases assump_65
  case intro assump_66 assump_67 =>
    have assump_89 : (((p2 → p1) ∧ (p4 → p2)) → ((p2 → p2) ∨ (p2 ∨ False))) := by
      intro assump_73
      cases assump_73
      case intro assump_74 assump_75 =>
        apply Or.inl
        intro assump_80
        exact assump_80
    let assump_72 := assump_1 assump_89
    apply False.elim assump_72


variable (p1 p4 p3 p6 p2 p0 p5 : Prop)
theorem file68_56229 : (((((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) → False) → ((((False ∨ False) ∧ (p5 → p6)) ∨ ((p1 ∧ p4) ∨ (True ∨ p3))) → (((p6 ∧ p2) ∧ (False ∨ p3)) ∧ ((p2 ∨ p4) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        apply False.elim assump_8
  case inr assump_4 =>
    cases assump_4
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        have assump_258 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_24
          apply False.elim assump_24
        let assump_23 := assump_1 assump_258
        apply False.elim assump_23
    case inr assump_14 =>
      cases assump_14
      case inl assump_30 =>
        have assump_259 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_37
          apply False.elim assump_37
        let assump_36 := assump_1 assump_259
        apply False.elim assump_36
      case inr assump_31 =>
        have assump_260 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_48
          apply False.elim assump_48
        let assump_47 := assump_1 assump_260
        apply False.elim assump_47
  cases assump_2
  case inl assump_54 =>
    cases assump_54
    case intro assump_56 assump_57 =>
      cases assump_56
      case inl assump_58 =>
        apply False.elim assump_58
      case inr assump_59 =>
        apply False.elim assump_59
  case inr assump_55 =>
    cases assump_55
    case inl assump_64 =>
      cases assump_64
      case intro assump_66 assump_67 =>
        have assump_261 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_75
          apply False.elim assump_75
        let assump_74 := assump_1 assump_261
        apply False.elim assump_74
    case inr assump_65 =>
      cases assump_65
      case inl assump_81 =>
        have assump_262 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_88
          apply False.elim assump_88
        let assump_87 := assump_1 assump_262
        apply False.elim assump_87
      case inr assump_82 =>
        have assump_263 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_99
          apply False.elim assump_99
        let assump_98 := assump_1 assump_263
        apply False.elim assump_98
  cases assump_2
  case inl assump_105 =>
    cases assump_105
    case intro assump_107 assump_108 =>
      cases assump_107
      case inl assump_109 =>
        apply False.elim assump_109
      case inr assump_110 =>
        apply False.elim assump_110
  case inr assump_106 =>
    cases assump_106
    case inl assump_115 =>
      cases assump_115
      case intro assump_117 assump_118 =>
        have assump_264 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_126
          apply False.elim assump_126
        let assump_125 := assump_1 assump_264
        apply False.elim assump_125
    case inr assump_116 =>
      cases assump_116
      case inl assump_132 =>
        have assump_265 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_139
          apply False.elim assump_139
        let assump_138 := assump_1 assump_265
        apply False.elim assump_138
      case inr assump_133 =>
        apply Or.inr
        exact assump_133
  intro assump_149
  cases assump_149
  case inl assump_150 =>
    cases assump_2
    case inl assump_154 =>
      cases assump_154
      case intro assump_156 assump_157 =>
        cases assump_156
        case inl assump_158 =>
          apply False.elim assump_158
        case inr assump_159 =>
          apply False.elim assump_159
    case inr assump_155 =>
      cases assump_155
      case inl assump_164 =>
        cases assump_164
        case intro assump_166 assump_167 =>
          have assump_266 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_175
            apply False.elim assump_175
          let assump_174 := assump_1 assump_266
          apply False.elim assump_174
      case inr assump_165 =>
        cases assump_165
        case inl assump_181 =>
          have assump_267 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_188
            apply False.elim assump_188
          let assump_187 := assump_1 assump_267
          apply False.elim assump_187
        case inr assump_182 =>
          have assump_268 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_199
            apply False.elim assump_199
          let assump_198 := assump_1 assump_268
          apply False.elim assump_198
  case inr assump_151 =>
    cases assump_2
    case inl assump_207 =>
      cases assump_207
      case intro assump_209 assump_210 =>
        cases assump_209
        case inl assump_211 =>
          apply False.elim assump_211
        case inr assump_212 =>
          apply False.elim assump_212
    case inr assump_208 =>
      cases assump_208
      case inl assump_217 =>
        cases assump_217
        case intro assump_219 assump_220 =>
          have assump_269 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_228
            apply False.elim assump_228
          let assump_227 := assump_1 assump_269
          apply False.elim assump_227
      case inr assump_218 =>
        cases assump_218
        case inl assump_234 =>
          have assump_270 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_241
            apply False.elim assump_241
          let assump_240 := assump_1 assump_270
          apply False.elim assump_240
        case inr assump_235 =>
          have assump_271 : (((p5 ∧ p0) ∨ (False → False)) ∨ ((p0 ∧ p0) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_252
            apply False.elim assump_252
          let assump_251 := assump_1 assump_271
          apply False.elim assump_251


variable (p6 p7 p3 p4 p1 p5 p0 : Prop)
theorem file68_63202 : (((((p6 → False) → (p7 ∧ p6)) → False) → (((p3 ∧ p6) → False) ∧ ((False ∨ False) ∨ (p6 → p3)))) ∨ ((((p3 → False) → (p0 → p5)) ∧ ((p6 → False) → (True → False))) ∧ (((p5 ∨ p4) → (False ∧ p1)) → ((False → p0) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_43 : ((p6 → False) → (p7 ∧ p6)) := by
      intro assump_12
      apply And.intro
      have assump_44 : p6 := by
        exact assump_4
      let assump_15 := assump_12 assump_44
      apply False.elim assump_15
      exact assump_4
    let assump_11 := assump_1 assump_43
    apply False.elim assump_11
  apply Or.inr
  intro assump_26
  have assump_45 : ((p6 → False) → (p7 ∧ p6)) := by
    intro assump_31
    apply And.intro
    have assump_46 : p6 := by
      exact assump_26
    let assump_34 := assump_31 assump_46
    apply False.elim assump_34
    exact assump_26
  let assump_30 := assump_1 assump_45
  apply False.elim assump_30


variable (p7 p3 p6 p1 p2 p5 p0 : Prop)
theorem file68_64266 : (((((False → False) ∨ (p5 → False)) ∧ ((p0 ∧ p5) ∨ (p3 → False))) → False) → ((((p3 → False) → (p1 → True)) ∨ ((p3 ∧ p2) ∨ (p7 ∨ p7))) ∨ (((p6 → p1) → False) ∨ ((p1 → False) → (True ∨ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p1 p7 p5 p2 p4 p3 : Prop)
theorem file68_64624 : ((((((p1 ∨ p1) → False) ∧ ((p1 ∧ p4) → False)) → False) ∧ ((((p3 → False) ∧ (p3 ∧ p1)) → ((p7 ∧ p5) → (p4 ∧ p2))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_62 : (((p3 → False) ∧ (p3 ∧ p1)) → ((p7 ∧ p5) → (p4 ∧ p2))) := by
      intro assump_13
      intro assump_14
      apply And.intro
      cases assump_14
      case intro assump_15 assump_16 =>
        cases assump_13
        case intro assump_21 assump_22 =>
          cases assump_22
          case intro assump_25 assump_26 =>
            have assump_63 : p3 := by
              exact assump_25
            let assump_33 := assump_21 assump_63
            apply False.elim assump_33
      cases assump_14
      case intro assump_37 assump_38 =>
        cases assump_13
        case intro assump_43 assump_44 =>
          cases assump_44
          case intro assump_47 assump_48 =>
            have assump_64 : p3 := by
              exact assump_47
            let assump_55 := assump_43 assump_64
            apply False.elim assump_55
    let assump_12 := assump_7 assump_62
    apply False.elim assump_12


variable (p6 p0 p3 p5 p7 p2 : Prop)
theorem file68_65818 : ((((((p0 ∨ p5) → (p2 → p2)) ∧ ((p3 ∨ True) ∨ (p0 ∧ False))) ∨ (((p7 → False) ∧ (p0 ∧ False)) → ((False ∨ p6) ∧ (p6 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∨ p5) → (p2 → p2)) ∧ ((p3 ∨ True) ∨ (p0 ∧ False))) ∨ (((p7 → False) ∧ (p0 ∧ False)) → ((False ∨ p6) ∧ (p6 ∨ p6)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      exact assump_6
    case inr assump_10 =>
      exact assump_6
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p7 p1 p4 p5 p2 p6 : Prop)
theorem file68_66500 : (((((p3 ∨ p7) → False) → False) → (((p1 → False) ∨ (p1 → False)) → ((p1 ∧ p7) ∧ (p3 ∨ False)))) → ((((p4 → p7) ∨ (p5 ∨ p1)) → False) → (((True → False) → (p1 ∧ p2)) ∨ ((False → p6) ∧ (p1 ∨ p6))))) := by
  intro assump_30
  intro assump_31
  apply Or.inl
  intro assump_36
  apply And.intro
  have assump_49 : True := by
    apply True.intro
  let assump_39 := assump_36 assump_49
  apply False.elim assump_39
  have assump_50 : True := by
    apply True.intro
  let assump_45 := assump_36 assump_50
  apply False.elim assump_45


variable (p0 p7 p3 p6 p4 : Prop)
theorem file68_67085 : ((((((p6 ∧ False) → False) → False) → False) → ((((p0 → True) → False) → ((p3 ∨ p7) ∧ (True ∧ p4))) → False)) → False) := by
  intro assump_1
  have assump_38 : ((((p6 ∧ False) → False) → False) → False) := by
    intro assump_5
    have assump_39 : ((p6 ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_5 assump_39
    apply False.elim assump_8
  let assump_4 := assump_1 assump_38
  have assump_40 : (((p0 → True) → False) → ((p3 ∨ p7) ∧ (True ∧ p4))) := by
    intro assump_20
    apply And.intro
    have assump_41 : (p0 → True) := by
      intro assump_24
      apply True.intro
    let assump_23 := assump_20 assump_41
    apply False.elim assump_23
    apply And.intro
    apply True.intro
    have assump_42 : (p0 → True) := by
      intro assump_31
      apply True.intro
    let assump_30 := assump_20 assump_42
    apply False.elim assump_30
  let assump_19 := assump_4 assump_40
  apply False.elim assump_19


variable (p0 p5 p2 p7 p1 : Prop)
theorem file68_68181 : (((((p7 ∧ p5) ∧ (p7 ∨ p7)) → ((p2 → p1) → (p5 → True))) → False) → ((((p2 → False) ∧ (p0 → True)) → ((p0 ∧ p0) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p7 ∧ p5) ∧ (p7 ∨ p7)) → ((p2 → p1) → (p5 → True))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    apply True.intro
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p6 p7 p5 p2 p1 p4 p0 : Prop)
theorem file68_68647 : (((((p2 ∨ True) ∧ (p2 ∧ False)) → ((p7 ∧ False) → (p5 → p2))) ∧ (((p0 → p4) → (p7 → p1)) ∧ ((p6 ∨ p4) → False))) → ((((p2 ∨ p6) → (p1 → p0)) → ((p1 → False) ∧ (p5 ∧ p5))) → (((p0 → p4) → (p6 → False)) ∨ ((p4 → p5) ∨ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply Or.inl
      intro assump_15
      intro assump_16
      have assump_27 : (p6 ∨ p4) := by
        apply Or.inl
        exact assump_16
      let assump_23 := assump_10 assump_27
      apply False.elim assump_23


variable (p3 p4 p6 p5 p0 p1 : Prop)
theorem file68_69310 : (((((p0 ∨ True) → False) → False) → False) → ((((p6 ∨ p0) ∨ (p0 ∧ p6)) ∧ ((p6 ∨ p5) ∨ (p4 ∨ p1))) ∨ (((p5 ∨ p3) → False) → ((True → False) → False)))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  intro assump_5
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_5 assump_15
  apply False.elim assump_11


variable (p0 p4 p7 p2 p5 p3 p6 : Prop)
theorem file68_69714 : (((((p7 → p2) ∧ (p7 ∧ False)) → ((True ∨ p7) → False)) ∨ (((p4 ∨ p3) ∨ (p6 → False)) ∨ ((p5 → False) → False))) ∨ ((((p0 → False) → (True → False)) → False) ∧ (((p5 ∨ p7) ∨ (p0 → p0)) ∧ ((p7 → p5) ∨ (p0 ∨ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  case inr assump_4 =>
    cases assump_1
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_24


variable (p3 p6 p1 p4 p5 p0 : Prop)
theorem file68_70425 : (((((False → p6) → False) ∧ ((p3 → p1) ∧ (p5 → False))) → False) ∨ ((((False → False) → (p0 → p4)) ∧ ((p6 → False) → (p3 → False))) ∧ (((p5 → True) → (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_21 : (False → p6) := by
        intro assump_15
        apply False.elim assump_15
      let assump_14 := assump_2 assump_21
      apply False.elim assump_14


variable (p4 p2 p0 p1 p5 p7 : Prop)
theorem file68_70983 : (((((p7 ∨ p5) ∧ (p4 → p1)) → ((True → p0) → (p2 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_24 : (((p7 ∨ p5) ∧ (p4 → p1)) → ((True → p0) → (p2 ∨ True))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p7 p6 p4 p1 p5 : Prop)
theorem file68_71551 : (((((p3 ∨ p1) → (p4 → False)) ∨ ((True ∧ True) → False)) → (((False ∧ p6) ∧ (p5 ∨ p7)) → False)) ∨ ((((p7 ∨ p3) → False) ∨ ((p6 ∧ p7) ∨ (False → False))) ∨ (((p6 ∨ p7) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p4 p1 p3 p6 p2 : Prop)
theorem file68_71989 : ((((((p3 ∨ p6) → False) ∧ ((p1 ∨ True) ∧ (p4 → False))) → (((False ∧ p6) ∨ (p3 ∨ p2)) ∨ ((p2 ∨ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_101 : ((((p3 ∨ p6) → False) ∧ ((p1 ∨ True) ∧ (p4 → False))) → (((False ∧ p6) ∨ (p3 ∨ p2)) ∨ ((p2 ∨ p3) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inr
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            have assump_102 : ((((p3 ∨ p6) → False) ∧ ((p1 ∨ True) ∧ (p4 → False))) → (((False ∧ p6) ∨ (p3 ∨ p2)) ∨ ((p2 ∨ p3) → False))) := by
              intro assump_28
              cases assump_28
              case intro assump_29 assump_30 =>
                cases assump_30
                case intro assump_33 assump_34 =>
                  cases assump_33
                  case inl assump_35 =>
                    apply Or.inl
                    apply Or.inr
                    apply Or.inr
                    exact assump_19
                  case inr assump_36 =>
                    apply Or.inl
                    apply Or.inr
                    apply Or.inr
                    exact assump_19
            let assump_27 := assump_1 assump_102
            apply False.elim assump_27
          case inr assump_20 =>
            have assump_103 : (p3 ∨ p6) := by
              apply Or.inl
              exact assump_20
            let assump_53 := assump_6 assump_103
            apply False.elim assump_53
        case inr assump_13 =>
          apply Or.inr
          intro assump_61
          cases assump_61
          case inl assump_62 =>
            have assump_104 : ((((p3 ∨ p6) → False) ∧ ((p1 ∨ True) ∧ (p4 → False))) → (((False ∧ p6) ∨ (p3 ∨ p2)) ∨ ((p2 ∨ p3) → False))) := by
              intro assump_70
              cases assump_70
              case intro assump_71 assump_72 =>
                cases assump_72
                case intro assump_75 assump_76 =>
                  cases assump_75
                  case inl assump_77 =>
                    apply Or.inl
                    apply Or.inr
                    apply Or.inr
                    exact assump_62
                  case inr assump_78 =>
                    apply Or.inl
                    apply Or.inr
                    apply Or.inr
                    exact assump_62
            let assump_69 := assump_1 assump_104
            apply False.elim assump_69
          case inr assump_63 =>
            have assump_105 : (p3 ∨ p6) := by
              apply Or.inl
              exact assump_63
            let assump_94 := assump_6 assump_105
            apply False.elim assump_94
  let assump_4 := assump_1 assump_101
  apply False.elim assump_4


variable (p0 p1 p2 : Prop)
theorem file68_74882 : (((((False ∧ p0) ∨ (p0 → p2)) → False) ∧ (((p2 ∧ False) ∨ (p0 ∨ p1)) → ((False ∧ p2) ∨ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : ((False ∧ p0) ∨ (p0 → p2)) := by
      apply Or.inr
      intro assump_10
      have assump_32 : ((p2 ∧ False) ∨ (p0 ∨ p1)) := by
        apply Or.inr
        apply Or.inl
        exact assump_10
      let assump_14 := assump_3 assump_32
      cases assump_14
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
      case inr assump_17 =>
        have assump_33 : True := by
          apply True.intro
        let assump_24 := assump_17 assump_33
        apply False.elim assump_24
    let assump_9 := assump_2 assump_31
    apply False.elim assump_9


variable (p7 p3 p1 p2 p0 : Prop)
theorem file68_75779 : (((((True → True) ∧ (p2 → False)) ∧ ((False → False) ∧ (True → False))) → False) ∨ ((((p1 → False) → (p3 ∨ p7)) → ((p0 → False) → False)) → (((False → p0) → (False → True)) ∨ ((p3 → p3) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_20 : True := by
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p5 p2 p1 p4 p7 p6 p3 : Prop)
theorem file68_76388 : (((((p7 → p7) ∨ (p5 → p1)) ∨ ((True → True) → False)) ∨ (((p3 → p6) → False) → ((p1 → False) → (p2 ∧ p6)))) ∨ ((((p4 → False) → False) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  exact assump_1


variable (p2 p4 p5 p3 p1 p6 p0 : Prop)
theorem file68_76705 : (((((p5 ∨ p0) → False) ∨ ((p3 ∨ p2) → (p1 → False))) → (((False → p5) ∧ (p3 ∨ p2)) → ((p0 ∧ p1) → False))) → ((((p5 → p6) → False) → ((p5 → True) ∨ (p6 → p6))) ∨ (((p4 → True) ∧ (p0 ∧ p4)) ∨ ((p4 ∨ p2) ∨ (p3 ∨ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  apply True.intro


variable (p2 p3 p1 p6 p4 p0 p5 : Prop)
theorem file68_77092 : (((((False ∧ p5) → (False ∨ p3)) → False) ∧ (((p3 ∧ p2) → False) ∨ ((p0 ∧ p2) → (p6 ∧ p1)))) → ((((p2 → p5) ∧ (p6 ∧ p1)) → ((p1 → False) → (p4 ∨ p5))) ∧ (((False ∧ p0) ∧ (True ∧ p4)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_1
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          have assump_53 : ((False ∧ p5) → (False ∨ p3)) := by
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              apply False.elim assump_27
          let assump_25 := assump_16 assump_53
          apply False.elim assump_25
        case inr assump_21 =>
          have assump_54 : ((False ∧ p5) → (False ∨ p3)) := by
            intro assump_38
            cases assump_38
            case intro assump_39 assump_40 =>
              apply False.elim assump_39
          let assump_37 := assump_16 assump_54
          apply False.elim assump_37
  intro assump_46
  cases assump_46
  case intro assump_47 assump_48 =>
    cases assump_47
    case intro assump_49 assump_50 =>
      apply False.elim assump_49


variable (p3 p7 p0 p2 p5 : Prop)
theorem file68_78414 : ((((((p5 → False) → (True ∨ p2)) ∧ ((p7 ∨ p3) ∧ (p3 ∨ p0))) → False) ∧ ((((p3 ∨ True) ∨ (p5 ∧ False)) → False) ∧ (((p0 ∧ False) → False) ∨ ((p3 ∧ True) → (False ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_26 : ((p3 ∨ True) ∨ (p5 ∧ False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_15 := assump_6 assump_26
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_27 : ((p3 ∨ True) ∨ (p5 ∧ False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_22 := assump_6 assump_27
        apply False.elim assump_22


variable (p0 p5 p2 p3 p6 p1 : Prop)
theorem file68_79284 : ((((((False → False) → False) ∨ ((p1 ∧ p0) ∨ (True ∨ p3))) → False) ∧ ((((p2 ∧ p3) ∨ (False → p3)) → ((False → False) ∧ (p6 → False))) ∧ (((p0 ∨ False) ∧ (p5 → False)) ∧ ((p6 → True) → False)))) → False) := by
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
          case inl assump_14 =>
            have assump_29 : (p6 → True) := by
              intro assump_23
              apply True.intro
            let assump_22 := assump_11 assump_29
            apply False.elim assump_22
          case inr assump_15 =>
            apply False.elim assump_15


variable (p7 p5 p1 p6 p2 : Prop)
theorem file68_80126 : ((((((p7 → True) ∨ (p2 → p6)) → False) → (((True ∨ p6) ∨ (p1 → p2)) → ((p5 ∨ p5) ∨ (False → p7)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p7 → True) ∨ (p2 → p6)) → False) → (((True ∨ p6) ∨ (p1 → p2)) → ((p5 ∨ p5) ∨ (False → p7)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inr
        intro assump_15
        apply False.elim assump_15
      case inr assump_10 =>
        apply Or.inr
        intro assump_22
        apply False.elim assump_22
    case inr assump_8 =>
      apply Or.inr
      intro assump_29
      apply False.elim assump_29
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p6 p3 p2 p4 p1 p0 p7 p5 : Prop)
theorem file68_80936 : ((((((p7 ∨ p5) → False) ∧ ((p5 → False) → False)) → (((p3 ∧ True) ∨ (p4 → True)) ∨ ((p0 → p2) → (p1 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p7 ∨ p5) → False) ∧ ((p5 → False) → False)) → (((p3 ∧ True) ∨ (p4 → True)) ∨ ((p0 → p2) → (p1 ∨ p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_12
      apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p5 p4 p2 p3 p0 p1 : Prop)
theorem file68_81503 : (((((p3 → p1) ∨ (p1 ∧ p6)) → False) ∧ (((p2 ∧ p5) ∧ (p5 → False)) ∨ ((p5 ∧ p4) ∧ (False ∧ p0)))) → ((((False → p0) ∧ (p2 ∨ False)) → False) ∧ (((p5 ∨ p4) ∧ (True ∧ False)) ∧ ((True ∧ p0) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              have assump_144 : p5 := by
                exact assump_20
              let assump_27 := assump_18 assump_144
              apply False.elim assump_27
        case inr assump_16 =>
          cases assump_16
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              cases assump_32
              case intro assump_39 assump_40 =>
                apply False.elim assump_39
    case inr assump_8 =>
      apply False.elim assump_8
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_46
    case inl assump_49 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          apply Or.inl
          exact assump_54
    case inr assump_50 =>
      cases assump_50
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          cases assump_62
          case intro assump_69 assump_70 =>
            apply False.elim assump_69
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_73 assump_74 =>
    cases assump_74
    case inl assump_77 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_79
        case intro assump_81 assump_82 =>
          have assump_145 : p5 := by
            exact assump_82
          let assump_89 := assump_80 assump_145
          apply False.elim assump_89
    case inr assump_78 =>
      cases assump_78
      case intro assump_93 assump_94 =>
        cases assump_93
        case intro assump_95 assump_96 =>
          cases assump_94
          case intro assump_101 assump_102 =>
            apply False.elim assump_101
  intro assump_105
  cases assump_105
  case intro assump_106 assump_107 =>
    cases assump_1
    case intro assump_112 assump_113 =>
      cases assump_113
      case inl assump_116 =>
        cases assump_116
        case intro assump_118 assump_119 =>
          cases assump_118
          case intro assump_120 assump_121 =>
            have assump_146 : p5 := by
              exact assump_121
            let assump_128 := assump_119 assump_146
            apply False.elim assump_128
      case inr assump_117 =>
        cases assump_117
        case intro assump_132 assump_133 =>
          cases assump_132
          case intro assump_134 assump_135 =>
            cases assump_133
            case intro assump_140 assump_141 =>
              apply False.elim assump_140


variable (p7 p3 p0 p6 p1 p4 : Prop)
theorem file68_84728 : (((((p1 ∧ True) ∨ (p4 ∨ p3)) ∨ ((False ∧ p7) → (p0 ∧ p4))) → (((p1 → p4) → False) ∧ ((p4 ∧ p6) → False))) → ((((True → False) ∧ (p3 ∨ p7)) → ((p0 ∨ p6) ∨ (p6 ∧ False))) ∨ (((p3 ∧ p1) ∧ (True ∨ p0)) ∧ ((p6 ∧ p4) → False)))) := by
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


variable (p7 p0 p1 p2 : Prop)
theorem file68_85449 : (((((p7 → True) ∨ (False → False)) ∨ ((True ∨ p1) ∨ (p0 → p2))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p7 → True) ∨ (False → False)) ∨ ((True ∨ p1) ∨ (p0 → p2))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p5 p6 p0 p7 p1 : Prop)
theorem file68_85838 : (((((p6 ∨ True) → False) ∧ ((True → p0) ∨ (p5 → p0))) → False) ∨ ((((p5 ∨ p1) → False) ∨ ((p5 → p2) → (p7 ∧ p6))) ∨ (((p5 ∧ False) → (p7 ∨ p2)) ∧ ((p5 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_23 : (p6 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_2 assump_23
      apply False.elim assump_12
    case inr assump_7 =>
      have assump_24 : (p6 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_19 := assump_2 assump_24
      apply False.elim assump_19


variable (p1 p3 p6 : Prop)
theorem file68_86543 : ((((((p1 ∧ p1) ∧ (True ∨ True)) ∨ ((p1 → True) ∨ (p1 ∨ p3))) ∨ (((p6 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p1 ∧ p1) ∧ (True ∨ True)) ∨ ((p1 → True) ∨ (p1 ∨ p3))) ∨ (((p6 → False) → False) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p4 p0 p7 p5 : Prop)
theorem file68_87009 : (((((True ∨ p0) ∧ (p4 → False)) → False) ∧ (((False → False) → False) ∨ ((p7 ∧ p5) ∧ (p5 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_31 : (False → False) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_6 assump_31
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          have assump_32 : p5 := by
            exact assump_20
          let assump_27 := assump_18 assump_32
          apply False.elim assump_27


variable (p3 p0 p1 p7 p6 : Prop)
theorem file68_87773 : (((((p1 ∨ True) ∨ (p3 → p0)) ∨ ((p7 ∨ p7) ∧ (True ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p1 ∨ True) ∨ (p3 → p0)) ∨ ((p7 ∨ p7) ∧ (True ∨ p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p1 p6 p7 p3 : Prop)
theorem file68_88145 : (((((True → False) ∧ (p6 → False)) ∧ ((True → p7) → False)) → False) → ((((p7 ∨ p2) → (p2 → p2)) ∨ ((p3 → False) ∧ (p3 → p1))) ∨ (((p2 → False) → False) ∨ ((p3 ∧ p2) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    exact assump_5
  case inr assump_9 =>
    exact assump_9


variable (p7 p6 p0 p5 p1 p2 p4 : Prop)
theorem file68_88574 : (((((p6 ∨ p0) ∧ (p5 → False)) ∧ ((p1 → False) ∨ (p4 → False))) ∨ (((p7 ∨ p1) → False) → ((False ∧ False) → False))) ∨ ((((p7 → p4) → (True → False)) ∧ ((p2 → False) → False)) → (((p0 → False) → (True → False)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p3 p5 p4 p0 p7 p6 p1 : Prop)
theorem file68_89009 : (((((p3 ∨ False) → (p1 → p7)) → False) ∨ (((p6 ∧ p4) ∧ (True ∨ p0)) ∨ ((True → False) → False))) → ((((True → True) → False) → ((p0 → False) → (p6 ∨ p3))) ∨ (((True ∧ p5) → (p3 ∨ p7)) → ((p5 → p6) → (True ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    have assump_58 : (True → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_6 assump_58
    apply False.elim assump_12
  case inr assump_3 =>
    cases assump_3
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_20
          case inl assump_27 =>
            apply Or.inl
            intro assump_31
            intro assump_32
            apply Or.inl
            exact assump_21
          case inr assump_28 =>
            apply Or.inl
            intro assump_39
            intro assump_40
            apply Or.inl
            exact assump_21
    case inr assump_18 =>
      apply Or.inl
      intro assump_47
      intro assump_48
      have assump_59 : (True → True) := by
        intro assump_54
        apply True.intro
      let assump_53 := assump_47 assump_59
      apply False.elim assump_53


variable (p1 p0 p3 : Prop)
theorem file68_90361 : ((((((p1 → False) → False) → ((False → p1) ∨ (p1 ∨ False))) ∨ (((p3 → p0) ∨ (p0 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 → False) → False) → ((False → p1) ∨ (p1 ∨ False))) ∨ (((p3 → p0) ∨ (p0 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p0 p5 p4 p2 p3 : Prop)
theorem file68_90852 : ((((((p4 ∧ True) ∨ (True ∨ p4)) ∨ ((p6 ∨ p3) ∨ (p4 → False))) ∨ (((p3 ∨ p3) → (p2 → p3)) → ((p3 → False) ∨ (p5 ∨ p0)))) → False) → False) := by
  intro assump_9
  have assump_16 : ((((p4 ∧ True) ∨ (True ∨ p4)) ∨ ((p6 ∨ p3) ∨ (p4 → False))) ∨ (((p3 ∨ p3) → (p2 → p3)) → ((p3 → False) ∨ (p5 ∨ p0)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_12 := assump_9 assump_16
  apply False.elim assump_12


variable (p6 p7 p2 p5 : Prop)
theorem file68_91366 : (((((p2 → True) → False) → ((p7 → p5) → (True ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p2 → True) → False) → ((p7 → p5) → (True ∧ p6))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply True.intro
    have assump_20 : (p2 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_5 assump_20
    apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p5 p2 p3 p0 p7 p4 : Prop)
theorem file68_91900 : ((((((False ∨ p1) ∨ (p7 ∧ p3)) ∧ ((True → False) ∧ (p4 → False))) ∧ (((p3 → p3) ∧ (True → False)) ∨ ((p5 → False) ∧ (p2 ∧ p0)))) ∧ ((((p2 → p5) → (True → False)) → ((p7 ∨ p0) ∨ (p2 → p2))) → False)) → False) := by
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
              cases assump_5
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  have assump_109 : (((p2 → p5) → (True → False)) → ((p7 ∨ p0) ∨ (p2 → p2))) := by
                    intro assump_33
                    apply Or.inr
                    intro assump_36
                    exact assump_36
                  let assump_32 := assump_3 assump_109
                  apply False.elim assump_32
              case inr assump_23 =>
                cases assump_23
                case intro assump_42 assump_43 =>
                  cases assump_43
                  case intro assump_46 assump_47 =>
                    have assump_110 : (((p2 → p5) → (True → False)) → ((p7 ∨ p0) ∨ (p2 → p2))) := by
                      intro assump_55
                      apply Or.inl
                      apply Or.inr
                      exact assump_47
                    let assump_54 := assump_3 assump_110
                    apply False.elim assump_54
        case inr assump_9 =>
          cases assump_9
          case intro assump_61 assump_62 =>
            cases assump_7
            case intro assump_67 assump_68 =>
              cases assump_5
              case inl assump_73 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  have assump_111 : (((p2 → p5) → (True → False)) → ((p7 ∨ p0) ∨ (p2 → p2))) := by
                    intro assump_84
                    apply Or.inl
                    apply Or.inl
                    exact assump_61
                  let assump_83 := assump_3 assump_111
                  apply False.elim assump_83
              case inr assump_74 =>
                cases assump_74
                case intro assump_90 assump_91 =>
                  cases assump_91
                  case intro assump_94 assump_95 =>
                    have assump_112 : (((p2 → p5) → (True → False)) → ((p7 ∨ p0) ∨ (p2 → p2))) := by
                      intro assump_103
                      apply Or.inl
                      apply Or.inl
                      exact assump_61
                    let assump_102 := assump_3 assump_112
                    apply False.elim assump_102


variable (p3 p5 p7 p4 p2 p0 : Prop)
theorem file68_94864 : (((((False ∨ p4) ∧ (p3 ∧ p7)) → ((p5 → p4) ∨ (p5 → p3))) → False) → ((((p2 → False) ∧ (p5 ∧ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_29 : (((False ∨ p4) ∧ (p3 ∧ p7)) → ((p5 → p4) ∨ (p5 → p3))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply Or.inl
          intro assump_23
          exact assump_12
  let assump_7 := assump_1 assump_29
  apply False.elim assump_7


variable (p3 p0 p4 p7 p2 : Prop)
theorem file68_95550 : ((((((False ∨ p4) ∨ (True → False)) → False) ∧ (((False → False) ∨ (p2 ∧ True)) ∨ ((p7 → p0) → False))) ∧ ((((p2 ∧ p0) → (p7 → p4)) → ((p7 → False) → (False → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_55 : (((p2 ∧ p0) → (p7 → p4)) → ((p7 → False) → (False → p3))) := by
            intro assump_17
            intro assump_18
            intro assump_19
            apply False.elim assump_19
          let assump_16 := assump_3 assump_55
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case intro assump_25 assump_26 =>
            have assump_56 : (((p2 ∧ p0) → (p7 → p4)) → ((p7 → False) → (False → p3))) := by
              intro assump_34
              intro assump_35
              intro assump_36
              apply False.elim assump_36
            let assump_33 := assump_3 assump_56
            apply False.elim assump_33
      case inr assump_9 =>
        have assump_57 : (((p2 ∧ p0) → (p7 → p4)) → ((p7 → False) → (False → p3))) := by
          intro assump_47
          intro assump_48
          intro assump_49
          apply False.elim assump_49
        let assump_46 := assump_3 assump_57
        apply False.elim assump_46


variable (p7 p3 p4 p5 : Prop)
theorem file68_97036 : (((((True → True) → False) → ((p7 ∧ p4) ∧ (p5 → p4))) ∧ (((True → False) → (p3 → False)) → ((p5 ∨ True) → (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : ((True → False) → (p3 → False)) := by
      intro assump_9
      intro assump_10
      have assump_25 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_25
      apply False.elim assump_15
    let assump_8 := assump_3 assump_24
    have assump_26 : (p5 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_19 := assump_8 assump_26
    have assump_27 : True := by
      apply True.intro
    let assump_20 := assump_19 assump_27
    apply False.elim assump_20


variable (p3 p5 p4 p2 p7 : Prop)
theorem file68_97823 : (((((p7 ∨ p2) ∨ (p5 ∨ p7)) → ((False ∧ p4) → (p5 → p3))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p7 ∨ p2) ∨ (p5 ∨ p7)) → ((False ∧ p4) → (p5 → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p1 p2 p0 p4 p7 p6 : Prop)
theorem file68_98276 : (((((False → p2) → False) ∧ ((p5 ∨ p6) → (False ∧ p2))) → (((p6 → p0) → (p0 → False)) → ((p4 → False) → (p2 → False)))) ∨ ((((p1 ∨ p7) → (p6 ∨ p1)) → False) → (((p7 → False) → (p7 → False)) → ((p4 ∨ p5) → (p6 ∧ p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    have assump_25 : (False → p2) := by
      intro assump_19
      apply False.elim assump_19
    let assump_18 := assump_11 assump_25
    apply False.elim assump_18


variable (p1 p2 p6 p3 : Prop)
theorem file68_98858 : ((((((False ∨ p6) ∧ (p3 ∧ False)) → False) ∧ (((p1 ∨ p1) ∨ (p2 → p6)) → False)) ∧ ((((True → False) ∧ (p6 ∨ p2)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_37 : (((True → False) ∧ (p6 ∨ p2)) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            have assump_38 : True := by
              apply True.intro
            let assump_23 := assump_14 assump_38
            apply False.elim assump_23
          case inr assump_19 =>
            have assump_39 : True := by
              apply True.intro
            let assump_30 := assump_14 assump_39
            apply False.elim assump_30
      let assump_12 := assump_3 assump_37
      apply False.elim assump_12


variable (p1 p5 p4 p3 p6 p2 : Prop)
theorem file68_99829 : (((((p1 → p1) → (p1 → False)) → ((False → False) ∨ (False ∧ p4))) ∨ (((p5 → p5) ∧ (p6 ∨ True)) ∧ ((True ∨ p6) ∧ (True → p5)))) ∧ ((((p3 → False) → (False → True)) → ((p1 ∧ False) → False)) ∨ (((p6 → False) → (True ∧ p3)) ∧ ((p2 ∧ p5) ∨ (p4 ∨ p3))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p7 p0 p4 p5 : Prop)
theorem file68_100381 : (((((p0 → p5) ∧ (True ∧ p4)) → ((p7 ∨ p4) ∨ (p5 → p4))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p0 → p5) ∧ (True ∧ p4)) → ((p7 ∨ p4) ∨ (p5 → p4))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inr
        exact assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p0 p2 p4 p1 p6 p7 : Prop)
theorem file68_100886 : ((((((p5 ∨ p2) ∧ (p7 → p4)) ∧ ((p4 ∧ p4) → (p0 → False))) ∧ (((p6 ∨ False) → False) ∧ ((p5 → False) → False))) ∧ ((((False → p6) ∨ (True ∨ p5)) ∨ ((p7 ∨ p1) ∧ (p1 → False))) → False)) → False) := by
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
          case inl assump_10 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              have assump_54 : (((False → p6) ∨ (True ∨ p5)) ∨ ((p7 ∨ p1) ∧ (p1 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_3 assump_54
              apply False.elim assump_26
          case inr assump_11 =>
            cases assump_5
            case intro assump_39 assump_40 =>
              have assump_55 : (((False → p6) ∨ (True ∨ p5)) ∨ ((p7 ∨ p1) ∧ (p1 → False))) := by
                apply Or.inl
                apply Or.inl
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_3 assump_55
              apply False.elim assump_47


variable (p3 p7 p1 p2 p4 p5 : Prop)
theorem file68_102267 : (((((True ∨ p4) ∨ (p1 → False)) → ((False → False) → False)) → False) ∨ ((((False → False) ∧ (False ∨ p5)) → False) → (((True → p7) → (p7 ∧ p4)) → ((p3 ∨ p3) ∨ (p7 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((True ∨ p4) ∨ (p1 → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_12
  have assump_13 : (False → False) := by
    intro assump_6
    apply False.elim assump_6
  let assump_5 := assump_4 assump_13
  apply False.elim assump_5


variable (p1 p3 p4 : Prop)
theorem file68_102831 : (((((p3 → False) → False) → ((True ∨ False) ∧ (False → p4))) → False) → ((((p1 → p1) ∧ (p4 ∧ False)) → False) → False)) := by
  intro assump_9
  intro assump_10
  have assump_25 : (((p3 → False) → False) → ((True ∨ False) ∧ (False → p4))) := by
    intro assump_16
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_19
    apply False.elim assump_19
  let assump_15 := assump_9 assump_25
  apply False.elim assump_15


variable (p1 p2 p0 p5 p6 p4 p7 : Prop)
theorem file68_103335 : ((((((p7 ∧ False) → False) → ((p2 → False) → (p7 ∧ p5))) → (((p0 ∨ p4) → (p6 → False)) ∧ ((p0 → False) → False))) ∧ ((((p1 ∧ True) ∨ (False → False)) ∨ ((False ∨ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p1 ∧ True) ∨ (False → False)) ∨ ((False ∨ p7) → False)) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p5 p1 p4 : Prop)
theorem file68_103904 : ((((((p5 → True) → False) ∧ ((True ∨ p4) ∨ (p4 ∨ p1))) → False) ∧ ((((p5 ∨ p4) → False) → ((p5 → False) → (False ∨ p1))) ∧ (((False → p5) → False) ∧ ((p7 ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : (False → p5) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_10 assump_24
        apply False.elim assump_17


variable (p5 p7 p0 p4 p2 p6 p3 p1 : Prop)
theorem file68_104531 : (((((p4 → False) → (p4 → p5)) ∨ ((p3 ∧ p4) → False)) ∨ (((p6 → False) → (p4 ∨ p1)) ∨ ((p2 ∧ p5) → (False → False)))) ∨ ((((p2 → p7) → (p2 → False)) → False) → (((p1 ∨ p2) → False) ∧ ((p7 → p0) ∧ (False ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_75
  intro assump_76
  have assump_85 : p4 := by
    exact assump_76
  let assump_81 := assump_75 assump_85
  apply False.elim assump_81


variable (p4 p5 p1 p7 p0 p2 p3 : Prop)
theorem file68_105009 : ((((((p2 ∨ p4) → (p0 ∨ p5)) ∧ ((p2 → False) → (p1 ∨ p3))) → (((p3 ∧ True) ∧ (p2 ∧ True)) ∨ ((p5 ∧ p7) → (p3 → p5)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p2 ∨ p4) → (p0 ∨ p5)) ∧ ((p2 → False) → (p1 ∨ p3))) → (((p3 ∧ True) ∧ (p2 ∧ True)) ∨ ((p5 ∧ p7) → (p3 → p5)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      intro assump_13
      cases assump_12
      case intro assump_16 assump_17 =>
        exact assump_16
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


