variable (p0 p3 p2 p6 p1 p7 : Prop)
theorem file87_44 : (((((p2 ∨ True) ∨ (True → False)) ∨ ((False ∧ p1) → False)) → False) → ((((p1 → p1) ∧ (p3 ∧ p1)) ∨ ((p7 → True) → (False ∧ False))) ∨ (((p0 → False) → False) ∧ ((p7 → False) ∧ (p6 ∨ p2))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inr
  intro assump_11
  apply And.intro
  have assump_26 : (((p2 ∨ True) ∨ (True → False)) ∨ ((False ∧ p1) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_15 := assump_5 assump_26
  apply False.elim assump_15
  have assump_27 : (((p2 ∨ True) ∨ (True → False)) ∨ ((False ∧ p1) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_22 := assump_5 assump_27
  apply False.elim assump_22


variable (p7 p1 p2 p6 p5 : Prop)
theorem file87_824 : ((((((p5 ∨ p6) ∧ (p1 ∨ p2)) → False) → (((True ∨ p7) → False) → False)) ∧ ((((p5 → False) ∧ (p6 ∨ p1)) → ((p1 ∧ p7) ∨ (p1 ∨ p6))) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    have assump_40 : (((p5 → False) ∧ (p6 ∨ p1)) → ((p1 ∧ p7) ∨ (p1 ∨ p6))) := by
      intro assump_26
      cases assump_26
      case intro assump_27 assump_28 =>
        cases assump_28
        case inl assump_31 =>
          apply Or.inr
          apply Or.inr
          exact assump_31
        case inr assump_32 =>
          apply Or.inr
          apply Or.inl
          exact assump_32
    let assump_25 := assump_20 assump_40
    apply False.elim assump_25


variable (p0 p5 p3 p2 p7 p4 : Prop)
theorem file87_1577 : ((((((p4 → False) ∧ (False ∧ p0)) ∧ ((p7 → p5) → (p5 ∨ p2))) ∧ (((p5 → False) → (True → False)) → ((p2 ∧ p4) ∨ (p4 ∧ p3)))) ∧ ((((True → p5) ∨ (p0 → p5)) → False) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p1 p4 p5 p6 p3 p7 : Prop)
theorem file87_2178 : ((((((False → p6) → (p4 ∨ p4)) → False) → (((p3 → True) ∨ (p4 ∧ p7)) ∨ ((p5 → False) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False → p6) → (p4 ∨ p4)) → False) → (((p3 → True) ∨ (p4 ∧ p7)) ∨ ((p5 → False) ∧ (p1 → False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p3 p1 p5 p2 p7 : Prop)
theorem file87_2666 : ((((((p5 ∨ p4) → (p7 → p5)) → False) → False) ∧ ((((p3 ∧ p7) ∨ (p4 ∧ p1)) ∨ ((p2 → False) → (True → False))) ∧ (((False ∧ p7) → (False → p7)) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            have assump_56 : ((False ∧ p7) → (False → p7)) := by
              intro assump_21
              intro assump_22
              apply False.elim assump_22
            let assump_20 := assump_7 assump_56
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case intro assump_28 assump_29 =>
            have assump_57 : ((False ∧ p7) → (False → p7)) := by
              intro assump_37
              intro assump_38
              apply False.elim assump_38
            let assump_36 := assump_7 assump_57
            apply False.elim assump_36
      case inr assump_9 =>
        have assump_58 : ((False ∧ p7) → (False → p7)) := by
          intro assump_49
          intro assump_50
          apply False.elim assump_50
        let assump_48 := assump_7 assump_58
        apply False.elim assump_48


variable (p7 p5 p1 p2 p4 : Prop)
theorem file87_4047 : ((((((False ∧ p7) ∨ (True ∨ p7)) ∨ ((p1 → False) → False)) ∨ (((p2 ∨ p7) → (True ∨ p4)) ∨ ((p5 → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((False ∧ p7) ∨ (True ∨ p7)) ∨ ((p1 → False) → False)) ∨ (((p2 ∨ p7) → (True ∨ p4)) ∨ ((p5 → p2) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p4 p1 p2 p3 p5 p0 p7 : Prop)
theorem file87_4553 : (((((True → False) → False) ∨ ((p0 → p3) → (p2 ∨ p7))) ∨ (((p0 → False) → False) → False)) ∨ ((((False → True) → False) → ((p5 ∧ p4) ∧ (True ∨ p4))) ∨ (((True → p6) ∨ (p7 ∨ p1)) ∧ ((True ∨ p1) ∧ (p5 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p5 p7 p1 p0 p6 p4 : Prop)
theorem file87_5010 : (((((p4 ∧ p4) → False) ∧ ((True ∨ p5) → False)) ∧ (((p5 ∧ p2) ∨ (p7 → p6)) ∨ ((p1 → False) ∨ (p0 ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_58 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_22 := assump_5 assump_58
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_59 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_29 := assump_5 assump_59
          apply False.elim assump_29
      case inr assump_11 =>
        cases assump_11
        case inl assump_33 =>
          have assump_60 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_38 := assump_5 assump_60
          apply False.elim assump_38
        case inr assump_34 =>
          cases assump_34
          case inl assump_42 =>
            have assump_61 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_47 := assump_5 assump_61
            apply False.elim assump_47
          case inr assump_43 =>
            have assump_62 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_54 := assump_5 assump_62
            apply False.elim assump_54


theorem file87_6623 : ((((((True → False) → False) → False) → False) → False) → False) := by
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


variable (p0 p6 p5 p3 p4 : Prop)
theorem file87_7198 : (((((p5 ∨ p4) ∨ (False → False)) → False) → False) ∨ ((((p4 ∨ p5) → (False ∧ p5)) → False) ∧ (((True ∨ p3) → (p6 ∨ p0)) → ((p4 ∨ p5) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p5 ∨ p4) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p1 p4 p6 p5 p3 : Prop)
theorem file87_7627 : (((((p4 ∨ p6) ∧ (p4 → False)) → ((p1 → False) ∧ (p5 → False))) → (((True → False) → (p7 → True)) ∨ ((p1 ∧ p5) → (p3 → False)))) ∨ ((((p5 ∧ p4) ∧ (p6 → False)) → ((p3 ∨ False) → False)) → (((p5 → p5) → False) → ((p4 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p5 p2 p3 p6 p4 p0 p7 : Prop)
theorem file87_8032 : ((((((p3 ∧ p0) ∧ (False ∧ True)) → False) → (((p2 ∧ p7) ∧ (False ∨ p5)) ∧ ((False ∧ False) → (p6 → False)))) ∧ ((((p0 ∧ p4) → (p5 → p5)) → False) ∧ (((p0 → p4) ∨ (p6 ∨ p3)) ∨ ((p2 → False) ∧ (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_89 : ((p0 ∧ p4) → (p5 → p5)) := by
            intro assump_18
            intro assump_19
            cases assump_18
            case intro assump_22 assump_23 =>
              exact assump_19
          let assump_17 := assump_6 assump_89
          apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case inl assump_31 =>
            have assump_90 : ((p0 ∧ p4) → (p5 → p5)) := by
              intro assump_37
              intro assump_38
              cases assump_37
              case intro assump_41 assump_42 =>
                exact assump_38
            let assump_36 := assump_6 assump_90
            apply False.elim assump_36
          case inr assump_32 =>
            have assump_91 : ((p0 ∧ p4) → (p5 → p5)) := by
              intro assump_54
              intro assump_55
              cases assump_54
              case intro assump_58 assump_59 =>
                exact assump_55
            let assump_53 := assump_6 assump_91
            apply False.elim assump_53
      case inr assump_11 =>
        cases assump_11
        case intro assump_67 assump_68 =>
          have assump_92 : ((p0 ∧ p4) → (p5 → p5)) := by
            intro assump_76
            intro assump_77
            cases assump_76
            case intro assump_80 assump_81 =>
              exact assump_77
          let assump_75 := assump_6 assump_92
          apply False.elim assump_75


variable (p1 p5 p0 p4 p2 p7 : Prop)
theorem file87_9987 : ((((((False → p4) ∨ (p1 ∨ p2)) ∨ ((p5 ∧ p7) → (p0 ∨ p7))) ∨ (((True ∨ p4) ∨ (p5 ∧ p0)) ∧ ((p7 → False) → (True ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → p4) ∨ (p1 ∨ p2)) ∨ ((p5 ∧ p7) → (p0 ∨ p7))) ∨ (((True ∨ p4) ∨ (p5 ∧ p0)) ∧ ((p7 → False) → (True ∨ p5)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p3 p1 p6 p4 p0 : Prop)
theorem file87_10516 : (((((p1 → False) ∨ (p2 ∧ p1)) ∧ ((p4 → False) ∨ (p3 ∨ p2))) ∧ (((p1 → True) → False) ∧ ((p6 ∨ p0) ∨ (p2 ∨ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                have assump_288 : (p1 → True) := by
                  intro assump_26
                  apply True.intro
                let assump_25 := assump_14 assump_288
                apply False.elim assump_25
              case inr assump_21 =>
                have assump_289 : (p1 → True) := by
                  intro assump_34
                  apply True.intro
                let assump_33 := assump_14 assump_289
                apply False.elim assump_33
            case inr assump_19 =>
              cases assump_19
              case inl assump_38 =>
                have assump_290 : (p1 → True) := by
                  intro assump_44
                  apply True.intro
                let assump_43 := assump_14 assump_290
                apply False.elim assump_43
              case inr assump_39 =>
                have assump_291 : (p1 → True) := by
                  intro assump_52
                  apply True.intro
                let assump_51 := assump_14 assump_291
                apply False.elim assump_51
        case inr assump_11 =>
          cases assump_11
          case inl assump_56 =>
            cases assump_3
            case intro assump_60 assump_61 =>
              cases assump_61
              case inl assump_64 =>
                cases assump_64
                case inl assump_66 =>
                  have assump_292 : (p1 → True) := by
                    intro assump_72
                    apply True.intro
                  let assump_71 := assump_60 assump_292
                  apply False.elim assump_71
                case inr assump_67 =>
                  have assump_293 : (p1 → True) := by
                    intro assump_80
                    apply True.intro
                  let assump_79 := assump_60 assump_293
                  apply False.elim assump_79
              case inr assump_65 =>
                cases assump_65
                case inl assump_84 =>
                  have assump_294 : (p1 → True) := by
                    intro assump_90
                    apply True.intro
                  let assump_89 := assump_60 assump_294
                  apply False.elim assump_89
                case inr assump_85 =>
                  have assump_295 : (p1 → True) := by
                    intro assump_98
                    apply True.intro
                  let assump_97 := assump_60 assump_295
                  apply False.elim assump_97
          case inr assump_57 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_105
              case inl assump_108 =>
                cases assump_108
                case inl assump_110 =>
                  have assump_296 : (p1 → True) := by
                    intro assump_116
                    apply True.intro
                  let assump_115 := assump_104 assump_296
                  apply False.elim assump_115
                case inr assump_111 =>
                  have assump_297 : (p1 → True) := by
                    intro assump_124
                    apply True.intro
                  let assump_123 := assump_104 assump_297
                  apply False.elim assump_123
              case inr assump_109 =>
                cases assump_109
                case inl assump_128 =>
                  have assump_298 : (p1 → True) := by
                    intro assump_134
                    apply True.intro
                  let assump_133 := assump_104 assump_298
                  apply False.elim assump_133
                case inr assump_129 =>
                  have assump_299 : (p1 → True) := by
                    intro assump_142
                    apply True.intro
                  let assump_141 := assump_104 assump_299
                  apply False.elim assump_141
      case inr assump_7 =>
        cases assump_7
        case intro assump_146 assump_147 =>
          cases assump_5
          case inl assump_152 =>
            cases assump_3
            case intro assump_156 assump_157 =>
              cases assump_157
              case inl assump_160 =>
                cases assump_160
                case inl assump_162 =>
                  have assump_300 : (p1 → True) := by
                    intro assump_168
                    apply True.intro
                  let assump_167 := assump_156 assump_300
                  apply False.elim assump_167
                case inr assump_163 =>
                  have assump_301 : (p1 → True) := by
                    intro assump_176
                    apply True.intro
                  let assump_175 := assump_156 assump_301
                  apply False.elim assump_175
              case inr assump_161 =>
                cases assump_161
                case inl assump_180 =>
                  have assump_302 : (p1 → True) := by
                    intro assump_186
                    apply True.intro
                  let assump_185 := assump_156 assump_302
                  apply False.elim assump_185
                case inr assump_181 =>
                  have assump_303 : (p1 → True) := by
                    intro assump_194
                    apply True.intro
                  let assump_193 := assump_156 assump_303
                  apply False.elim assump_193
          case inr assump_153 =>
            cases assump_153
            case inl assump_198 =>
              cases assump_3
              case intro assump_202 assump_203 =>
                cases assump_203
                case inl assump_206 =>
                  cases assump_206
                  case inl assump_208 =>
                    have assump_304 : (p1 → True) := by
                      intro assump_214
                      apply True.intro
                    let assump_213 := assump_202 assump_304
                    apply False.elim assump_213
                  case inr assump_209 =>
                    have assump_305 : (p1 → True) := by
                      intro assump_222
                      apply True.intro
                    let assump_221 := assump_202 assump_305
                    apply False.elim assump_221
                case inr assump_207 =>
                  cases assump_207
                  case inl assump_226 =>
                    have assump_306 : (p1 → True) := by
                      intro assump_232
                      apply True.intro
                    let assump_231 := assump_202 assump_306
                    apply False.elim assump_231
                  case inr assump_227 =>
                    have assump_307 : (p1 → True) := by
                      intro assump_240
                      apply True.intro
                    let assump_239 := assump_202 assump_307
                    apply False.elim assump_239
            case inr assump_199 =>
              cases assump_3
              case intro assump_246 assump_247 =>
                cases assump_247
                case inl assump_250 =>
                  cases assump_250
                  case inl assump_252 =>
                    have assump_308 : (p1 → True) := by
                      intro assump_258
                      apply True.intro
                    let assump_257 := assump_246 assump_308
                    apply False.elim assump_257
                  case inr assump_253 =>
                    have assump_309 : (p1 → True) := by
                      intro assump_266
                      apply True.intro
                    let assump_265 := assump_246 assump_309
                    apply False.elim assump_265
                case inr assump_251 =>
                  cases assump_251
                  case inl assump_270 =>
                    have assump_310 : (p1 → True) := by
                      intro assump_276
                      apply True.intro
                    let assump_275 := assump_246 assump_310
                    apply False.elim assump_275
                  case inr assump_271 =>
                    have assump_311 : (p1 → True) := by
                      intro assump_284
                      apply True.intro
                    let assump_283 := assump_246 assump_311
                    apply False.elim assump_283


variable (p5 p2 p7 p0 p4 p3 : Prop)
theorem file87_19320 : ((((((p4 → False) → False) → False) ∧ (((p4 → False) ∧ (p0 ∧ p3)) → ((p4 ∧ p3) → (False ∧ p2)))) ∧ ((((p5 → False) → False) → False) ∧ (((False → False) ∨ (p7 ∨ p7)) → False))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_13
      case intro assump_20 assump_21 =>
        have assump_33 : ((False → False) ∨ (p7 ∨ p7)) := by
          apply Or.inl
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_21 assump_33
        apply False.elim assump_26


variable (p0 p1 p6 p5 : Prop)
theorem file87_19985 : (((((True ∧ False) → (p1 ∧ p5)) → ((p6 → p0) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((True ∧ False) → (p1 ∧ p5)) → ((p6 → p0) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p0 p1 p6 p2 p7 p5 p4 : Prop)
theorem file87_20397 : (((((p7 → False) ∧ (p4 ∨ p4)) ∨ ((p6 → p6) → (True ∧ p5))) ∧ (((True → True) → False) ∧ ((p3 ∨ p0) ∨ (False → p2)))) → ((((p6 ∧ p1) → (p5 ∧ p1)) ∧ ((True ∨ p1) ∧ (p6 → True))) ∧ (((p0 ∧ p2) → (p5 → False)) → False))) := by
  intro assump_11
  apply And.intro
  apply And.intro
  intro assump_12
  apply And.intro
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_11
    case intro assump_19 assump_20 =>
      cases assump_19
      case inl assump_21 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_24
          case inl assump_27 =>
            cases assump_20
            case intro assump_31 assump_32 =>
              cases assump_32
              case inl assump_35 =>
                cases assump_35
                case inl assump_37 =>
                  have assump_369 : (True → True) := by
                    intro assump_43
                    apply True.intro
                  let assump_42 := assump_31 assump_369
                  apply False.elim assump_42
                case inr assump_38 =>
                  have assump_370 : (True → True) := by
                    intro assump_51
                    apply True.intro
                  let assump_50 := assump_31 assump_370
                  apply False.elim assump_50
              case inr assump_36 =>
                have assump_371 : (True → True) := by
                  intro assump_59
                  apply True.intro
                let assump_58 := assump_31 assump_371
                apply False.elim assump_58
          case inr assump_28 =>
            cases assump_20
            case intro assump_65 assump_66 =>
              cases assump_66
              case inl assump_69 =>
                cases assump_69
                case inl assump_71 =>
                  have assump_372 : (True → True) := by
                    intro assump_77
                    apply True.intro
                  let assump_76 := assump_65 assump_372
                  apply False.elim assump_76
                case inr assump_72 =>
                  have assump_373 : (True → True) := by
                    intro assump_85
                    apply True.intro
                  let assump_84 := assump_65 assump_373
                  apply False.elim assump_84
              case inr assump_70 =>
                have assump_374 : (True → True) := by
                  intro assump_93
                  apply True.intro
                let assump_92 := assump_65 assump_374
                apply False.elim assump_92
      case inr assump_22 =>
        cases assump_20
        case intro assump_99 assump_100 =>
          cases assump_100
          case inl assump_103 =>
            cases assump_103
            case inl assump_105 =>
              have assump_375 : (True → True) := by
                intro assump_111
                apply True.intro
              let assump_110 := assump_99 assump_375
              apply False.elim assump_110
            case inr assump_106 =>
              have assump_376 : (True → True) := by
                intro assump_119
                apply True.intro
              let assump_118 := assump_99 assump_376
              apply False.elim assump_118
          case inr assump_104 =>
            have assump_377 : (True → True) := by
              intro assump_127
              apply True.intro
            let assump_126 := assump_99 assump_377
            apply False.elim assump_126
  cases assump_12
  case intro assump_131 assump_132 =>
    cases assump_11
    case intro assump_137 assump_138 =>
      cases assump_137
      case inl assump_139 =>
        cases assump_139
        case intro assump_141 assump_142 =>
          cases assump_142
          case inl assump_145 =>
            cases assump_138
            case intro assump_149 assump_150 =>
              cases assump_150
              case inl assump_153 =>
                cases assump_153
                case inl assump_155 =>
                  exact assump_132
                case inr assump_156 =>
                  exact assump_132
              case inr assump_154 =>
                exact assump_132
          case inr assump_146 =>
            cases assump_138
            case intro assump_165 assump_166 =>
              cases assump_166
              case inl assump_169 =>
                cases assump_169
                case inl assump_171 =>
                  exact assump_132
                case inr assump_172 =>
                  exact assump_132
              case inr assump_170 =>
                exact assump_132
      case inr assump_140 =>
        cases assump_138
        case intro assump_181 assump_182 =>
          cases assump_182
          case inl assump_185 =>
            cases assump_185
            case inl assump_187 =>
              exact assump_132
            case inr assump_188 =>
              exact assump_132
          case inr assump_186 =>
            exact assump_132
  apply And.intro
  cases assump_11
  case intro assump_195 assump_196 =>
    cases assump_195
    case inl assump_197 =>
      cases assump_197
      case intro assump_199 assump_200 =>
        cases assump_200
        case inl assump_203 =>
          cases assump_196
          case intro assump_207 assump_208 =>
            cases assump_208
            case inl assump_211 =>
              cases assump_211
              case inl assump_213 =>
                apply Or.inl
                apply True.intro
              case inr assump_214 =>
                apply Or.inl
                apply True.intro
            case inr assump_212 =>
              apply Or.inl
              apply True.intro
        case inr assump_204 =>
          cases assump_196
          case intro assump_223 assump_224 =>
            cases assump_224
            case inl assump_227 =>
              cases assump_227
              case inl assump_229 =>
                apply Or.inl
                apply True.intro
              case inr assump_230 =>
                apply Or.inl
                apply True.intro
            case inr assump_228 =>
              apply Or.inl
              apply True.intro
    case inr assump_198 =>
      cases assump_196
      case intro assump_239 assump_240 =>
        cases assump_240
        case inl assump_243 =>
          cases assump_243
          case inl assump_245 =>
            apply Or.inl
            apply True.intro
          case inr assump_246 =>
            apply Or.inl
            apply True.intro
        case inr assump_244 =>
          apply Or.inl
          apply True.intro
  intro assump_253
  apply True.intro
  intro assump_254
  cases assump_11
  case intro assump_257 assump_258 =>
    cases assump_257
    case inl assump_259 =>
      cases assump_259
      case intro assump_261 assump_262 =>
        cases assump_262
        case inl assump_265 =>
          cases assump_258
          case intro assump_269 assump_270 =>
            cases assump_270
            case inl assump_273 =>
              cases assump_273
              case inl assump_275 =>
                have assump_378 : (True → True) := by
                  intro assump_281
                  apply True.intro
                let assump_280 := assump_269 assump_378
                apply False.elim assump_280
              case inr assump_276 =>
                have assump_379 : (True → True) := by
                  intro assump_289
                  apply True.intro
                let assump_288 := assump_269 assump_379
                apply False.elim assump_288
            case inr assump_274 =>
              have assump_380 : (True → True) := by
                intro assump_297
                apply True.intro
              let assump_296 := assump_269 assump_380
              apply False.elim assump_296
        case inr assump_266 =>
          cases assump_258
          case intro assump_303 assump_304 =>
            cases assump_304
            case inl assump_307 =>
              cases assump_307
              case inl assump_309 =>
                have assump_381 : (True → True) := by
                  intro assump_315
                  apply True.intro
                let assump_314 := assump_303 assump_381
                apply False.elim assump_314
              case inr assump_310 =>
                have assump_382 : (True → True) := by
                  intro assump_323
                  apply True.intro
                let assump_322 := assump_303 assump_382
                apply False.elim assump_322
            case inr assump_308 =>
              have assump_383 : (True → True) := by
                intro assump_331
                apply True.intro
              let assump_330 := assump_303 assump_383
              apply False.elim assump_330
    case inr assump_260 =>
      cases assump_258
      case intro assump_337 assump_338 =>
        cases assump_338
        case inl assump_341 =>
          cases assump_341
          case inl assump_343 =>
            have assump_384 : (True → True) := by
              intro assump_349
              apply True.intro
            let assump_348 := assump_337 assump_384
            apply False.elim assump_348
          case inr assump_344 =>
            have assump_385 : (True → True) := by
              intro assump_357
              apply True.intro
            let assump_356 := assump_337 assump_385
            apply False.elim assump_356
        case inr assump_342 =>
          have assump_386 : (True → True) := by
            intro assump_365
            apply True.intro
          let assump_364 := assump_337 assump_386
          apply False.elim assump_364


variable (p0 p6 p1 p2 : Prop)
theorem file87_30116 : ((((((True ∨ p6) ∧ (True ∧ False)) → False) ∨ (((True ∧ p1) ∧ (p2 ∨ p2)) → ((p2 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((True ∨ p6) ∧ (True ∧ False)) → False) ∨ (((True ∧ p1) ∧ (p2 ∨ p2)) → ((p2 ∧ p0) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p3 p5 p6 p2 p0 p1 p4 p7 : Prop)
theorem file87_30875 : (((((p3 → p0) → (False → False)) ∨ ((p5 ∨ p4) → (p6 ∨ False))) ∨ (((p4 ∨ p0) ∧ (p5 → False)) → False)) ∨ ((((p1 ∨ p2) → (p7 ∨ p2)) → ((p0 ∨ True) → False)) → (((p2 → False) → False) ∧ ((False → p4) → (p6 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p6 p3 p2 p1 p5 p4 p0 p7 : Prop)
theorem file87_31268 : ((((((p4 → False) → (p0 ∨ p1)) ∨ ((False ∧ p5) ∧ (p6 → False))) ∨ (((p7 ∨ p4) ∨ (p1 ∧ p1)) ∧ ((p2 ∨ p0) → (p5 → p3)))) ∧ ((((p2 ∧ False) → False) → ((p5 → False) → False)) ∧ (((False → False) ∧ (False → p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_102 : ((False → False) ∧ (False → p7)) := by
            apply And.intro
            intro assump_17
            apply False.elim assump_17
            intro assump_20
            apply False.elim assump_20
          let assump_16 := assump_11 assump_102
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
    case inr assump_5 =>
      cases assump_5
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          cases assump_34
          case inl assump_36 =>
            cases assump_3
            case intro assump_42 assump_43 =>
              have assump_103 : ((False → False) ∧ (False → p7)) := by
                apply And.intro
                intro assump_49
                apply False.elim assump_49
                intro assump_52
                apply False.elim assump_52
              let assump_48 := assump_43 assump_103
              apply False.elim assump_48
          case inr assump_37 =>
            cases assump_3
            case intro assump_62 assump_63 =>
              have assump_104 : ((False → False) ∧ (False → p7)) := by
                apply And.intro
                intro assump_69
                apply False.elim assump_69
                intro assump_72
                apply False.elim assump_72
              let assump_68 := assump_63 assump_104
              apply False.elim assump_68
        case inr assump_35 =>
          cases assump_35
          case intro assump_78 assump_79 =>
            cases assump_3
            case intro assump_86 assump_87 =>
              have assump_105 : ((False → False) ∧ (False → p7)) := by
                apply And.intro
                intro assump_93
                apply False.elim assump_93
                intro assump_96
                apply False.elim assump_96
              let assump_92 := assump_87 assump_105
              apply False.elim assump_92


variable (p0 p3 p2 p1 : Prop)
theorem file87_33883 : ((((((p1 → False) → False) → ((True → True) ∨ (p0 → p2))) ∨ (((p3 → False) → False) ∧ ((p2 ∧ p3) → (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p1 → False) → False) → ((True → True) ∨ (p0 → p2))) ∨ (((p3 → False) → False) ∧ ((p2 ∧ p3) → (p1 → p1)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p3 p7 p6 : Prop)
theorem file87_34383 : ((((((False → p3) → False) ∨ ((True ∧ False) ∧ (p7 → False))) → (((p6 → False) ∨ (p3 ∨ p5)) ∧ ((p6 ∨ True) → False))) → False) → False) := by
  intro assump_12
  have assump_88 : ((((False → p3) → False) ∨ ((True ∧ False) ∧ (p7 → False))) → (((p6 → False) ∨ (p3 ∨ p5)) ∧ ((p6 ∨ True) → False))) := by
    intro assump_16
    apply And.intro
    cases assump_16
    case inl assump_17 =>
      apply Or.inl
      intro assump_21
      have assump_89 : (False → p3) := by
        intro assump_26
        apply False.elim assump_26
      let assump_25 := assump_17 assump_89
      apply False.elim assump_25
    case inr assump_18 =>
      cases assump_18
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
    intro assump_40
    cases assump_40
    case inl assump_41 =>
      cases assump_16
      case inl assump_45 =>
        have assump_90 : (False → p3) := by
          intro assump_50
          apply False.elim assump_50
        let assump_49 := assump_45 assump_90
        apply False.elim assump_49
      case inr assump_46 =>
        cases assump_46
        case intro assump_56 assump_57 =>
          cases assump_56
          case intro assump_58 assump_59 =>
            apply False.elim assump_59
    case inr assump_42 =>
      cases assump_16
      case inl assump_66 =>
        have assump_91 : (False → p3) := by
          intro assump_71
          apply False.elim assump_71
        let assump_70 := assump_66 assump_91
        apply False.elim assump_70
      case inr assump_67 =>
        cases assump_67
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            apply False.elim assump_80
  let assump_15 := assump_12 assump_88
  apply False.elim assump_15


variable (p4 p2 p6 p5 p0 p7 : Prop)
theorem file87_36279 : ((((((True → p7) → False) ∨ ((True ∧ p0) → False)) → False) ∧ ((((p4 → False) ∨ (p5 ∧ p2)) → ((p0 → p0) ∨ (p6 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((p4 → False) ∨ (p5 ∧ p2)) → ((p0 → p0) ∨ (p6 → p7))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        exact assump_14
      case inr assump_11 =>
        cases assump_11
        case intro assump_17 assump_18 =>
          apply Or.inl
          intro assump_23
          exact assump_23
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p5 p2 p0 p4 p3 p7 : Prop)
theorem file87_37009 : (((((p3 → p2) → False) ∧ ((True → False) ∧ (False ∧ True))) → False) ∨ ((((p0 → p5) → (p3 ∨ True)) → ((p3 ∨ p3) ∧ (p4 → False))) ∨ (((p7 → False) → (p7 ∧ True)) ∧ ((p4 → p7) → False)))) := by
  apply Or.inl
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        apply False.elim assump_33


variable (p2 p6 : Prop)
theorem file87_37491 : (((((False ∧ p6) ∧ (p6 ∧ p6)) → ((False → p2) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : (((False ∧ p6) ∧ (p6 ∧ p6)) → ((False → p2) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p7 p4 p2 p6 p3 : Prop)
theorem file87_37982 : (((((False ∧ False) ∨ (True → False)) ∧ ((p5 → p2) ∨ (p5 → p7))) → (((p6 → p6) → (p3 ∨ p7)) → ((p2 → False) → False))) ∨ ((((p5 → p7) → False) → False) ∧ (((p3 → False) ∧ (False ∧ p6)) ∧ ((p4 → False) ∧ (p6 → True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
    case inr assump_11 =>
      cases assump_9
      case inl assump_18 =>
        have assump_34 : True := by
          apply True.intro
        let assump_23 := assump_11 assump_34
        apply False.elim assump_23
      case inr assump_19 =>
        have assump_35 : True := by
          apply True.intro
        let assump_30 := assump_11 assump_35
        apply False.elim assump_30


variable (p6 p7 p2 p3 p1 : Prop)
theorem file87_38912 : (((((False ∧ p7) ∨ (p7 ∨ False)) → False) → False) → ((((False → p3) ∧ (True ∨ p3)) ∨ ((True → p3) ∨ (p6 → True))) ∨ (((p2 ∨ p3) → False) → ((p1 → p6) ∨ (False → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  apply True.intro


variable (p0 p7 p5 p3 p1 p6 : Prop)
theorem file87_39295 : ((((((True → False) → (p1 ∧ False)) ∨ ((p3 → p5) ∧ (False → p6))) ∨ (((p3 ∧ False) ∨ (True ∧ p3)) → ((p7 → False) → (p0 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True → False) → (p1 ∧ False)) ∨ ((p3 → p5) ∧ (False → p6))) ∨ (((p3 ∧ False) ∨ (True ∧ p3)) → ((p7 → False) → (p0 ∨ p1)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply And.intro
    have assump_22 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_22
    apply False.elim assump_8
    have assump_23 : True := by
      apply True.intro
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p6 p2 p1 p0 p7 : Prop)
theorem file87_40065 : ((((((p3 → p3) → (p0 → True)) → ((p7 ∨ True) → (p6 → p6))) ∧ (((p6 ∧ p7) → (True ∨ p7)) ∨ ((p2 ∧ True) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p3 → p3) → (p0 → True)) → ((p7 ∨ True) → (p6 → p6))) ∧ (((p6 ∧ p7) → (True ∨ p7)) ∨ ((p2 ∧ True) ∧ (p1 → False)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      exact assump_7
    case inr assump_11 =>
      exact assump_7
    apply Or.inl
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p1 p6 p3 p4 p7 : Prop)
theorem file87_40823 : (((((False ∧ False) ∧ (p2 → True)) → False) ∧ (((p4 ∨ p4) → (p2 → False)) ∨ ((p6 ∨ p2) → (p7 ∨ p3)))) → ((((p1 ∨ True) → (True → False)) → ((p7 ∨ p2) ∨ (p7 ∧ False))) ∨ (((p7 ∧ True) ∧ (p2 → p7)) ∧ ((p2 ∧ False) ∧ (p3 ∨ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      have assump_28 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_10 assump_28
      have assump_29 : True := by
        apply True.intro
      let assump_14 := assump_13 assump_29
      apply False.elim assump_14
    case inr assump_7 =>
      apply Or.inl
      intro assump_20
      have assump_30 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_23 := assump_20 assump_30
      have assump_31 : True := by
        apply True.intro
      let assump_24 := assump_23 assump_31
      apply False.elim assump_24


variable (p7 p1 p2 : Prop)
theorem file87_41857 : (((((p7 ∧ p2) → (p7 ∧ True)) → ((p1 → False) → (True → True))) → False) → False) := by
  intro assump_7
  have assump_17 : (((p7 ∧ p2) → (p7 ∧ True)) → ((p1 → False) → (True → True))) := by
    intro assump_11
    intro assump_12
    intro assump_13
    apply True.intro
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p3 p0 p1 p5 p7 p4 p6 : Prop)
theorem file87_42258 : (((((p6 ∧ False) ∧ (p0 → False)) ∧ ((p0 ∨ True) ∨ (p6 ∨ True))) → False) ∨ ((((p6 → True) → (p3 ∧ p1)) ∧ ((p5 → False) → (p6 ∧ False))) → (((p7 ∨ p1) ∧ (p7 ∨ False)) ∧ ((p0 ∧ p4) ∨ (p1 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p4 p6 p7 p2 p1 p0 : Prop)
theorem file87_42753 : (((((False ∧ p4) → (False ∧ p0)) → False) ∧ (((False → True) ∨ (True → p7)) → False)) → ((((p1 ∧ p2) ∨ (p6 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : ((False → True) ∨ (True → p7)) := by
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_11 := assump_6 assump_16
    apply False.elim assump_11


variable (p4 p3 p6 p0 p5 p1 p7 p2 : Prop)
theorem file87_43239 : ((((((p2 ∧ False) → (p3 ∧ p7)) → False) → (((p4 ∧ p1) → (p6 → False)) ∧ ((p3 → False) ∨ (p5 ∨ p0)))) ∧ ((((p4 → False) ∨ (p5 → p6)) ∨ ((p7 ∨ p4) → False)) ∧ (((p0 ∨ p4) ∨ (False → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_39 : ((p0 ∨ p4) ∨ (False → True)) := by
            apply Or.inr
            intro assump_17
            apply True.intro
          let assump_16 := assump_7 assump_39
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_40 : ((p0 ∨ p4) ∨ (False → True)) := by
            apply Or.inr
            intro assump_26
            apply True.intro
          let assump_25 := assump_7 assump_40
          apply False.elim assump_25
      case inr assump_9 =>
        have assump_41 : ((p0 ∨ p4) ∨ (False → True)) := by
          apply Or.inr
          intro assump_35
          apply True.intro
        let assump_34 := assump_7 assump_41
        apply False.elim assump_34


variable (p6 p1 p4 p2 p3 p5 p0 : Prop)
theorem file87_44465 : (((((p6 → False) → (False → p1)) → False) → False) ∨ ((((True ∧ p2) ∨ (p0 ∧ p1)) → ((False ∧ p2) ∨ (p4 → False))) ∧ (((p5 ∨ p3) → (p5 → p1)) ∨ ((False ∨ p1) ∧ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p6 → False) → (False → p1)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p2 p5 p6 p1 p4 p3 p7 : Prop)
theorem file87_44933 : (((((True ∨ p6) ∨ (p0 → p0)) ∨ ((p3 → False) → False)) ∧ (((p5 ∧ p4) → False) → ((p5 → False) → (p2 → p2)))) ∨ ((((p5 → True) ∧ (p1 → p3)) → False) ∨ (((p0 → False) → (p7 ∨ p6)) → ((p4 → p2) ∨ (p2 → False))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_5
  intro assump_6
  intro assump_7
  exact assump_7


variable (p3 p7 p2 p5 p4 p6 p0 : Prop)
theorem file87_45377 : (((((p3 ∧ p4) ∧ (True ∧ False)) ∧ ((p2 ∧ True) → False)) ∧ (((True → p0) ∨ (p2 ∨ p7)) ∨ ((p2 ∨ p6) ∧ (p5 → True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p6 p2 p0 p3 p1 p7 p5 p4 : Prop)
theorem file87_45927 : (((((p3 ∨ True) → False) → ((p4 → p3) ∧ (p5 ∧ p7))) ∨ (((p1 ∨ p4) ∨ (p1 → p4)) → False)) ∨ ((((p6 ∧ p3) ∨ (p2 ∨ p1)) → ((p4 → False) → (p2 → p1))) ∨ (((p7 ∧ p1) → (p3 ∨ p7)) → ((p0 → p2) ∧ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_23 : (p3 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_23
  apply False.elim assump_7
  apply And.intro
  have assump_24 : (p3 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_13 := assump_1 assump_24
  apply False.elim assump_13
  have assump_25 : (p3 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_19 := assump_1 assump_25
  apply False.elim assump_19


variable (p7 p2 p6 p5 p4 p0 p1 : Prop)
theorem file87_46726 : (((((True → p6) → False) ∧ ((p1 → p6) ∧ (p2 → p5))) ∧ (((p1 → p5) ∧ (True ∨ False)) → False)) → ((((p2 ∧ False) → False) ∨ ((p7 → p4) ∨ (p5 → p6))) ∨ (((p0 ∧ False) ∨ (p5 → p4)) ∨ ((False → p2) ∧ (True → False))))) := by
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
        cases assump_16
        case intro assump_17 assump_18 =>
          apply False.elim assump_18


variable (p5 p6 p2 p4 p3 p0 : Prop)
theorem file87_47358 : ((((((True ∧ False) → (True → False)) ∨ ((p0 → False) ∨ (p0 → False))) ∨ (((p4 ∨ p5) ∨ (p0 → False)) → ((p3 ∧ p6) → (p2 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∧ False) → (True → False)) ∨ ((p0 → False) ∨ (p0 → False))) ∨ (((p4 ∨ p5) ∨ (p0 → False)) → ((p3 ∧ p6) → (p2 ∨ p3)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p7 p4 p5 p3 : Prop)
theorem file87_47963 : ((((((p1 → False) ∧ (p3 → p3)) ∨ ((p4 ∨ p5) → False)) → (((p7 → False) ∧ (False ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) ∧ (p3 → p3)) ∨ ((p4 ∨ p5) → False)) → (((p7 → False) ∧ (False ∧ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p2 : Prop)
theorem file87_48523 : (((((p5 ∧ p2) ∧ (True ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : (((p5 ∧ p2) ∧ (True ∧ False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p7 p4 p1 p5 p0 p2 p3 : Prop)
theorem file87_49035 : (((((p1 ∨ p0) ∨ (p6 → False)) ∧ ((p3 → False) ∨ (p1 ∧ p5))) → (((p5 → p5) → (p6 → p3)) → ((p3 ∧ p7) → (p4 ∨ p5)))) ∨ ((((True → False) → (p2 → p1)) ∧ ((p7 → False) → (p1 → False))) ∧ (((p4 → False) ∨ (False ∧ p5)) ∧ ((p1 → True) → (p2 → p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_13
          case inl assump_20 =>
            have assump_66 : p3 := by
              exact assump_4
            let assump_24 := assump_20 assump_66
            apply False.elim assump_24
          case inr assump_21 =>
            cases assump_21
            case intro assump_28 assump_29 =>
              apply Or.inr
              exact assump_29
        case inr assump_17 =>
          cases assump_13
          case inl assump_36 =>
            have assump_67 : p3 := by
              exact assump_4
            let assump_40 := assump_36 assump_67
            apply False.elim assump_40
          case inr assump_37 =>
            cases assump_37
            case intro assump_44 assump_45 =>
              apply Or.inr
              exact assump_45
      case inr assump_15 =>
        cases assump_13
        case inl assump_52 =>
          have assump_68 : p3 := by
            exact assump_4
          let assump_56 := assump_52 assump_68
          apply False.elim assump_56
        case inr assump_53 =>
          cases assump_53
          case intro assump_60 assump_61 =>
            apply Or.inr
            exact assump_61


variable (p3 p4 p6 p7 p0 p5 p2 : Prop)
theorem file87_50791 : ((((((False → p6) ∨ (p3 ∨ p4)) ∨ ((False ∨ p2) ∨ (False ∧ p7))) ∨ (((p7 → False) → False) ∧ ((p5 ∨ p5) → False))) ∧ ((((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) → False)) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case inl assump_23 =>
      cases assump_23
      case inl assump_25 =>
        cases assump_25
        case inl assump_27 =>
          have assump_205 : (((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) := by
            intro assump_34
            intro assump_35
            cases assump_35
            case intro assump_36 assump_37 =>
              cases assump_34
              case intro assump_42 assump_43 =>
                cases assump_43
                case intro assump_46 assump_47 =>
                  have assump_206 : p6 := by
                    exact assump_46
                  let assump_54 := assump_42 assump_206
                  apply False.elim assump_54
          let assump_33 := assump_22 assump_205
          apply False.elim assump_33
        case inr assump_28 =>
          cases assump_28
          case inl assump_61 =>
            have assump_207 : (((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) := by
              intro assump_68
              intro assump_69
              cases assump_69
              case intro assump_70 assump_71 =>
                cases assump_68
                case intro assump_76 assump_77 =>
                  cases assump_77
                  case intro assump_80 assump_81 =>
                    have assump_208 : p6 := by
                      exact assump_80
                    let assump_88 := assump_76 assump_208
                    apply False.elim assump_88
            let assump_67 := assump_22 assump_207
            apply False.elim assump_67
          case inr assump_62 =>
            have assump_209 : (((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) := by
              intro assump_100
              intro assump_101
              cases assump_101
              case intro assump_102 assump_103 =>
                cases assump_100
                case intro assump_108 assump_109 =>
                  cases assump_109
                  case intro assump_112 assump_113 =>
                    have assump_210 : p6 := by
                      exact assump_112
                    let assump_120 := assump_108 assump_210
                    apply False.elim assump_120
            let assump_99 := assump_22 assump_209
            apply False.elim assump_99
      case inr assump_26 =>
        cases assump_26
        case inl assump_127 =>
          cases assump_127
          case inl assump_129 =>
            apply False.elim assump_129
          case inr assump_130 =>
            have assump_211 : (((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) := by
              intro assump_138
              intro assump_139
              cases assump_139
              case intro assump_140 assump_141 =>
                cases assump_138
                case intro assump_146 assump_147 =>
                  cases assump_147
                  case intro assump_150 assump_151 =>
                    have assump_212 : p6 := by
                      exact assump_150
                    let assump_158 := assump_146 assump_212
                    apply False.elim assump_158
            let assump_137 := assump_22 assump_211
            apply False.elim assump_137
        case inr assump_128 =>
          cases assump_128
          case intro assump_165 assump_166 =>
            apply False.elim assump_165
    case inr assump_24 =>
      cases assump_24
      case intro assump_169 assump_170 =>
        have assump_213 : (((p6 → False) ∧ (p6 ∧ p4)) → ((p6 ∧ p0) → False)) := by
          intro assump_178
          intro assump_179
          cases assump_179
          case intro assump_180 assump_181 =>
            cases assump_178
            case intro assump_186 assump_187 =>
              cases assump_187
              case intro assump_190 assump_191 =>
                have assump_214 : p6 := by
                  exact assump_190
                let assump_198 := assump_186 assump_214
                apply False.elim assump_198
        let assump_177 := assump_22 assump_213
        apply False.elim assump_177


variable (p3 p5 p4 p1 p0 p2 : Prop)
theorem file87_55155 : (((((p1 → p2) ∧ (p4 → p2)) ∧ ((p2 → False) ∧ (p3 → False))) → False) → ((((True ∨ p5) ∨ (p4 ∨ p0)) ∨ ((True → False) ∨ (p0 ∧ p5))) ∨ (((p1 ∧ False) → False) ∨ ((p0 ∧ p0) → (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p0 p5 p1 p6 p7 p2 : Prop)
theorem file87_55506 : ((((((p6 ∧ p5) ∧ (p6 → p2)) → ((p0 ∨ p1) ∨ (True ∧ p5))) ∨ (((p0 ∨ p7) ∨ (True ∧ p1)) → False)) → False) → False) := by
  intro assump_15
  have assump_33 : ((((p6 ∧ p5) ∧ (p6 → p2)) → ((p0 ∨ p1) ∨ (True ∧ p5))) ∨ (((p0 ∨ p7) ∨ (True ∧ p1)) → False)) := by
    apply Or.inl
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply Or.inr
        apply And.intro
        apply True.intro
        exact assump_23
  let assump_18 := assump_15 assump_33
  apply False.elim assump_18


variable (p4 p7 p6 p0 p1 p3 : Prop)
theorem file87_56142 : ((((((p6 ∨ p7) → (p0 → p0)) ∨ ((False → True) → False)) ∨ (((True ∧ p4) ∨ (p3 ∧ p1)) → ((p1 ∧ p4) ∨ (p6 → False)))) ∧ ((((p0 → False) ∧ (p0 → False)) → False) ∧ (((False → False) → (False ∧ p6)) ∧ ((p4 ∧ p6) ∧ (p4 → p7))))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_16
        case intro assump_23 assump_24 =>
          cases assump_24
          case intro assump_27 assump_28 =>
            cases assump_28
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                have assump_117 : (False → False) := by
                  intro assump_46
                  apply False.elim assump_46
                let assump_45 := assump_27 assump_117
                let assump_49 := And.left assump_45
                apply False.elim assump_49
      case inr assump_20 =>
        cases assump_16
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            cases assump_60
            case intro assump_63 assump_64 =>
              cases assump_63
              case intro assump_65 assump_66 =>
                have assump_118 : (False → False) := by
                  intro assump_78
                  apply False.elim assump_78
                let assump_77 := assump_59 assump_118
                let assump_81 := And.left assump_77
                apply False.elim assump_81
    case inr assump_18 =>
      cases assump_16
      case intro assump_87 assump_88 =>
        cases assump_88
        case intro assump_91 assump_92 =>
          cases assump_92
          case intro assump_95 assump_96 =>
            cases assump_95
            case intro assump_97 assump_98 =>
              have assump_119 : (False → False) := by
                intro assump_110
                apply False.elim assump_110
              let assump_109 := assump_91 assump_119
              let assump_113 := And.left assump_109
              apply False.elim assump_113


variable (p7 p5 p4 p2 p0 p3 p1 : Prop)
theorem file87_58360 : (((((p4 → p7) → False) ∧ ((True ∨ p5) → False)) → False) ∨ ((((p3 ∨ p5) ∧ (p3 → False)) → ((p1 ∨ False) → (True ∧ False))) ∧ (((p2 ∨ p7) ∧ (True ∨ True)) ∧ ((p0 → p7) → (p1 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p4 p7 p1 p3 p5 p2 : Prop)
theorem file87_58842 : (((((True → False) ∧ (p7 ∧ p2)) ∧ ((p2 → p7) → False)) ∧ (((p7 ∧ p7) → (False ∧ p4)) ∧ ((p4 ∧ p5) → False))) → ((((p1 → True) ∧ (True ∨ p1)) → False) → (((p7 ∨ p3) ∧ (p5 → p4)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_15
              case intro assump_30 assump_31 =>
                have assump_76 : (p7 ∧ p7) := by
                  apply And.intro
                  exact assump_22
                  exact assump_22
                let assump_37 := assump_30 assump_76
                let assump_38 := And.left assump_37
                apply False.elim assump_38
    case inr assump_7 =>
      cases assump_1
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            cases assump_53
            case intro assump_56 assump_57 =>
              cases assump_49
              case intro assump_64 assump_65 =>
                have assump_77 : (p7 ∧ p7) := by
                  apply And.intro
                  exact assump_56
                  exact assump_56
                let assump_71 := assump_64 assump_77
                let assump_72 := And.left assump_71
                apply False.elim assump_72


variable (p7 p0 p3 p6 p5 p4 : Prop)
theorem file87_60563 : (((((False → False) → False) → False) → False) → ((((p5 → False) ∧ (False ∧ p5)) ∧ ((p4 → p3) → False)) ∨ (((p0 → False) → (p7 → False)) ∨ ((p6 ∧ p4) ∧ (p6 ∧ True))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_22
  intro assump_23
  have assump_44 : (((False → False) → False) → False) := by
    intro assump_31
    have assump_45 : (False → False) := by
      intro assump_35
      apply False.elim assump_35
    let assump_34 := assump_31 assump_45
    apply False.elim assump_34
  let assump_30 := assump_1 assump_44
  apply False.elim assump_30


variable (p0 p4 p2 p6 p7 p1 p5 : Prop)
theorem file87_61201 : (((((p4 → p2) ∧ (p6 → p5)) → ((p5 ∨ p7) → False)) ∧ (((True → False) ∧ (p4 → False)) ∧ ((p6 ∨ p0) → (p5 ∧ p6)))) → ((((True ∨ True) ∧ (p6 ∧ False)) ∨ ((p6 → p0) → False)) → (((p1 ∧ p2) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
      case inr assump_11 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          apply False.elim assump_23
  case inr assump_7 =>
    cases assump_1
    case intro assump_30 assump_31 =>
      cases assump_31
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          have assump_50 : True := by
            apply True.intro
          let assump_46 := assump_36 assump_50
          apply False.elim assump_46


variable (p4 p7 p2 p3 p0 p1 : Prop)
theorem file87_62258 : (((((False → p0) ∨ (p7 → False)) → False) → False) ∨ ((((p7 ∨ p3) → (p4 → False)) → False) → (((p1 ∧ p1) ∧ (False → False)) ∧ ((p2 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → p0) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p6 p5 p4 p3 p2 : Prop)
theorem file87_62693 : ((((((p5 → True) → False) ∧ ((p2 ∨ p1) ∨ (p4 ∧ p2))) → (((p1 → p3) → (p6 → p4)) → ((p2 → p2) ∧ (False ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_111 : ((((p5 → True) → False) ∧ ((p2 ∨ p1) ∨ (p4 ∧ p2))) → (((p1 → p3) → (p6 → p4)) → ((p2 → p2) ∧ (False ∧ p5)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          exact assump_18
        case inr assump_19 =>
          exact assump_7
      case inr assump_17 =>
        cases assump_17
        case intro assump_24 assump_25 =>
          exact assump_25
    apply And.intro
    cases assump_5
    case intro assump_32 assump_33 =>
      cases assump_33
      case inl assump_36 =>
        cases assump_36
        case inl assump_38 =>
          have assump_112 : (p5 → True) := by
            intro assump_44
            apply True.intro
          let assump_43 := assump_32 assump_112
          apply False.elim assump_43
        case inr assump_39 =>
          have assump_113 : (p5 → True) := by
            intro assump_52
            apply True.intro
          let assump_51 := assump_32 assump_113
          apply False.elim assump_51
      case inr assump_37 =>
        cases assump_37
        case intro assump_56 assump_57 =>
          have assump_114 : (p5 → True) := by
            intro assump_65
            apply True.intro
          let assump_64 := assump_32 assump_114
          apply False.elim assump_64
    cases assump_5
    case intro assump_71 assump_72 =>
      cases assump_72
      case inl assump_75 =>
        cases assump_75
        case inl assump_77 =>
          have assump_115 : (p5 → True) := by
            intro assump_83
            apply True.intro
          let assump_82 := assump_71 assump_115
          apply False.elim assump_82
        case inr assump_78 =>
          have assump_116 : (p5 → True) := by
            intro assump_91
            apply True.intro
          let assump_90 := assump_71 assump_116
          apply False.elim assump_90
      case inr assump_76 =>
        cases assump_76
        case intro assump_95 assump_96 =>
          have assump_117 : (p5 → True) := by
            intro assump_104
            apply True.intro
          let assump_103 := assump_71 assump_117
          apply False.elim assump_103
  let assump_4 := assump_1 assump_111
  apply False.elim assump_4


variable (p4 p2 p1 p6 p5 p3 : Prop)
theorem file87_65266 : ((((((p1 ∧ p6) ∨ (p4 → True)) ∧ ((p1 ∨ p5) ∨ (p2 → p1))) → (((p1 → True) ∨ (p3 → False)) ∨ ((p1 → p3) → (p1 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p1 ∧ p6) ∨ (p4 → True)) ∧ ((p1 ∨ p5) ∨ (p2 → p1))) → (((p1 → True) ∨ (p3 → False)) ∨ ((p1 → p3) → (p1 ∨ p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              apply Or.inl
              apply Or.inl
              intro assump_22
              apply True.intro
            case inr assump_19 =>
              apply Or.inl
              apply Or.inl
              intro assump_25
              apply True.intro
          case inr assump_17 =>
            apply Or.inl
            apply Or.inl
            intro assump_28
            apply True.intro
      case inr assump_9 =>
        cases assump_7
        case inl assump_31 =>
          cases assump_31
          case inl assump_33 =>
            apply Or.inl
            apply Or.inl
            intro assump_37
            apply True.intro
          case inr assump_34 =>
            apply Or.inl
            apply Or.inl
            intro assump_40
            apply True.intro
        case inr assump_32 =>
          apply Or.inl
          apply Or.inl
          intro assump_43
          apply True.intro
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p4 p1 p5 p3 p2 p0 p6 : Prop)
theorem file87_66914 : ((((((p6 ∨ p4) ∧ (p2 ∧ p6)) ∧ ((p1 ∨ p3) → (p2 → False))) ∧ (((False → False) ∨ (p0 → False)) ∧ ((p1 ∨ p2) ∨ (True ∧ p5)))) ∧ ((((p2 ∧ p2) → False) ∧ ((p2 → p2) → False)) ∧ (((True → False) ∨ (p1 ∧ True)) ∧ ((p1 ∨ p0) → False)))) → False) := by
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
            cases assump_9
            case intro assump_14 assump_15 =>
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_23
                  case inl assump_28 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_3
                      case intro assump_34 assump_35 =>
                        cases assump_34
                        case intro assump_36 assump_37 =>
                          cases assump_35
                          case intro assump_42 assump_43 =>
                            cases assump_42
                            case inl assump_44 =>
                              have assump_496 : (p1 ∨ p0) := by
                                apply Or.inl
                                exact assump_30
                              let assump_50 := assump_43 assump_496
                              apply False.elim assump_50
                            case inr assump_45 =>
                              cases assump_45
                              case intro assump_54 assump_55 =>
                                have assump_497 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_54
                                let assump_62 := assump_43 assump_497
                                apply False.elim assump_62
                    case inr assump_31 =>
                      cases assump_3
                      case intro assump_68 assump_69 =>
                        cases assump_68
                        case intro assump_70 assump_71 =>
                          cases assump_69
                          case intro assump_76 assump_77 =>
                            cases assump_76
                            case inl assump_78 =>
                              have assump_498 : True := by
                                apply True.intro
                              let assump_85 := assump_78 assump_498
                              apply False.elim assump_85
                            case inr assump_79 =>
                              cases assump_79
                              case intro assump_89 assump_90 =>
                                have assump_499 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_89
                                let assump_97 := assump_77 assump_499
                                apply False.elim assump_97
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_101 assump_102 =>
                      cases assump_3
                      case intro assump_107 assump_108 =>
                        cases assump_107
                        case intro assump_109 assump_110 =>
                          cases assump_108
                          case intro assump_115 assump_116 =>
                            cases assump_115
                            case inl assump_117 =>
                              have assump_500 : True := by
                                apply True.intro
                              let assump_124 := assump_117 assump_500
                              apply False.elim assump_124
                            case inr assump_118 =>
                              cases assump_118
                              case intro assump_128 assump_129 =>
                                have assump_501 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_128
                                let assump_136 := assump_116 assump_501
                                apply False.elim assump_136
                case inr assump_25 =>
                  cases assump_23
                  case inl assump_142 =>
                    cases assump_142
                    case inl assump_144 =>
                      cases assump_3
                      case intro assump_148 assump_149 =>
                        cases assump_148
                        case intro assump_150 assump_151 =>
                          cases assump_149
                          case intro assump_156 assump_157 =>
                            cases assump_156
                            case inl assump_158 =>
                              have assump_502 : (p1 ∨ p0) := by
                                apply Or.inl
                                exact assump_144
                              let assump_164 := assump_157 assump_502
                              apply False.elim assump_164
                            case inr assump_159 =>
                              cases assump_159
                              case intro assump_168 assump_169 =>
                                have assump_503 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_168
                                let assump_176 := assump_157 assump_503
                                apply False.elim assump_176
                    case inr assump_145 =>
                      cases assump_3
                      case intro assump_182 assump_183 =>
                        cases assump_182
                        case intro assump_184 assump_185 =>
                          cases assump_183
                          case intro assump_190 assump_191 =>
                            cases assump_190
                            case inl assump_192 =>
                              have assump_504 : True := by
                                apply True.intro
                              let assump_199 := assump_192 assump_504
                              apply False.elim assump_199
                            case inr assump_193 =>
                              cases assump_193
                              case intro assump_203 assump_204 =>
                                have assump_505 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_203
                                let assump_211 := assump_191 assump_505
                                apply False.elim assump_211
                  case inr assump_143 =>
                    cases assump_143
                    case intro assump_215 assump_216 =>
                      cases assump_3
                      case intro assump_221 assump_222 =>
                        cases assump_221
                        case intro assump_223 assump_224 =>
                          cases assump_222
                          case intro assump_229 assump_230 =>
                            cases assump_229
                            case inl assump_231 =>
                              have assump_506 : True := by
                                apply True.intro
                              let assump_238 := assump_231 assump_506
                              apply False.elim assump_238
                            case inr assump_232 =>
                              cases assump_232
                              case intro assump_242 assump_243 =>
                                have assump_507 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_242
                                let assump_250 := assump_230 assump_507
                                apply False.elim assump_250
          case inr assump_11 =>
            cases assump_9
            case intro assump_256 assump_257 =>
              cases assump_5
              case intro assump_264 assump_265 =>
                cases assump_264
                case inl assump_266 =>
                  cases assump_265
                  case inl assump_270 =>
                    cases assump_270
                    case inl assump_272 =>
                      cases assump_3
                      case intro assump_276 assump_277 =>
                        cases assump_276
                        case intro assump_278 assump_279 =>
                          cases assump_277
                          case intro assump_284 assump_285 =>
                            cases assump_284
                            case inl assump_286 =>
                              have assump_508 : (p1 ∨ p0) := by
                                apply Or.inl
                                exact assump_272
                              let assump_292 := assump_285 assump_508
                              apply False.elim assump_292
                            case inr assump_287 =>
                              cases assump_287
                              case intro assump_296 assump_297 =>
                                have assump_509 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_296
                                let assump_304 := assump_285 assump_509
                                apply False.elim assump_304
                    case inr assump_273 =>
                      cases assump_3
                      case intro assump_310 assump_311 =>
                        cases assump_310
                        case intro assump_312 assump_313 =>
                          cases assump_311
                          case intro assump_318 assump_319 =>
                            cases assump_318
                            case inl assump_320 =>
                              have assump_510 : True := by
                                apply True.intro
                              let assump_327 := assump_320 assump_510
                              apply False.elim assump_327
                            case inr assump_321 =>
                              cases assump_321
                              case intro assump_331 assump_332 =>
                                have assump_511 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_331
                                let assump_339 := assump_319 assump_511
                                apply False.elim assump_339
                  case inr assump_271 =>
                    cases assump_271
                    case intro assump_343 assump_344 =>
                      cases assump_3
                      case intro assump_349 assump_350 =>
                        cases assump_349
                        case intro assump_351 assump_352 =>
                          cases assump_350
                          case intro assump_357 assump_358 =>
                            cases assump_357
                            case inl assump_359 =>
                              have assump_512 : True := by
                                apply True.intro
                              let assump_366 := assump_359 assump_512
                              apply False.elim assump_366
                            case inr assump_360 =>
                              cases assump_360
                              case intro assump_370 assump_371 =>
                                have assump_513 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_370
                                let assump_378 := assump_358 assump_513
                                apply False.elim assump_378
                case inr assump_267 =>
                  cases assump_265
                  case inl assump_384 =>
                    cases assump_384
                    case inl assump_386 =>
                      cases assump_3
                      case intro assump_390 assump_391 =>
                        cases assump_390
                        case intro assump_392 assump_393 =>
                          cases assump_391
                          case intro assump_398 assump_399 =>
                            cases assump_398
                            case inl assump_400 =>
                              have assump_514 : (p1 ∨ p0) := by
                                apply Or.inl
                                exact assump_386
                              let assump_406 := assump_399 assump_514
                              apply False.elim assump_406
                            case inr assump_401 =>
                              cases assump_401
                              case intro assump_410 assump_411 =>
                                have assump_515 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_410
                                let assump_418 := assump_399 assump_515
                                apply False.elim assump_418
                    case inr assump_387 =>
                      cases assump_3
                      case intro assump_424 assump_425 =>
                        cases assump_424
                        case intro assump_426 assump_427 =>
                          cases assump_425
                          case intro assump_432 assump_433 =>
                            cases assump_432
                            case inl assump_434 =>
                              have assump_516 : True := by
                                apply True.intro
                              let assump_441 := assump_434 assump_516
                              apply False.elim assump_441
                            case inr assump_435 =>
                              cases assump_435
                              case intro assump_445 assump_446 =>
                                have assump_517 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_445
                                let assump_453 := assump_433 assump_517
                                apply False.elim assump_453
                  case inr assump_385 =>
                    cases assump_385
                    case intro assump_457 assump_458 =>
                      cases assump_3
                      case intro assump_463 assump_464 =>
                        cases assump_463
                        case intro assump_465 assump_466 =>
                          cases assump_464
                          case intro assump_471 assump_472 =>
                            cases assump_471
                            case inl assump_473 =>
                              have assump_518 : True := by
                                apply True.intro
                              let assump_480 := assump_473 assump_518
                              apply False.elim assump_480
                            case inr assump_474 =>
                              cases assump_474
                              case intro assump_484 assump_485 =>
                                have assump_519 : (p1 ∨ p0) := by
                                  apply Or.inl
                                  exact assump_484
                                let assump_492 := assump_472 assump_519
                                apply False.elim assump_492


variable (p2 p6 p0 p5 : Prop)
theorem file87_82667 : (((((False → p5) → False) → ((p0 → p6) ∨ (p2 → False))) → False) → False) := by
  intro assump_13
  have assump_34 : (((False → p5) → False) → ((p0 → p6) ∨ (p2 → False))) := by
    intro assump_17
    apply Or.inl
    intro assump_20
    have assump_35 : (False → p5) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_17 assump_35
    apply False.elim assump_24
  let assump_16 := assump_13 assump_34
  apply False.elim assump_16


variable (p4 p2 p1 p6 p5 p3 : Prop)
theorem file87_83196 : ((((((p1 → p5) → False) ∧ ((p5 ∧ p3) → False)) ∨ (((p5 ∧ p4) ∨ (p6 ∧ p4)) ∧ ((True → False) ∧ (False → p4)))) ∧ ((((p1 ∧ p2) ∨ (p2 → False)) → ((p6 ∨ True) ∨ (p3 ∧ p4))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        have assump_95 : (((p1 ∧ p2) ∨ (p2 → False)) → ((p6 ∨ True) ∨ (p3 ∧ p4))) := by
          intro assump_19
          cases assump_19
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
          case inr assump_21 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
        let assump_18 := assump_7 assump_95
        apply False.elim assump_18
    case inr assump_9 =>
      cases assump_9
      case intro assump_33 assump_34 =>
        cases assump_33
        case inl assump_35 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            cases assump_34
            case intro assump_43 assump_44 =>
              have assump_96 : (((p1 ∧ p2) ∨ (p2 → False)) → ((p6 ∨ True) ∨ (p3 ∧ p4))) := by
                intro assump_52
                cases assump_52
                case inl assump_53 =>
                  cases assump_53
                  case intro assump_55 assump_56 =>
                    apply Or.inl
                    apply Or.inr
                    apply True.intro
                case inr assump_54 =>
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
              let assump_51 := assump_7 assump_96
              apply False.elim assump_51
        case inr assump_36 =>
          cases assump_36
          case intro assump_66 assump_67 =>
            cases assump_34
            case intro assump_72 assump_73 =>
              have assump_97 : (((p1 ∧ p2) ∨ (p2 → False)) → ((p6 ∨ True) ∨ (p3 ∧ p4))) := by
                intro assump_81
                cases assump_81
                case inl assump_82 =>
                  cases assump_82
                  case intro assump_84 assump_85 =>
                    apply Or.inl
                    apply Or.inl
                    exact assump_66
                case inr assump_83 =>
                  apply Or.inl
                  apply Or.inl
                  exact assump_66
              let assump_80 := assump_7 assump_97
              apply False.elim assump_80


variable (p5 p3 p7 p6 p4 p1 p0 p2 : Prop)
theorem file87_85829 : (((((p0 ∨ p2) → (p3 ∧ p0)) ∧ ((p7 → False) ∨ (p3 → p3))) → (((p3 ∨ p5) → False) → ((p5 ∧ p1) → False))) ∨ ((((p5 → False) → False) ∧ ((p7 → False) → False)) ∨ (((p1 → p4) → False) ∧ ((False ∨ True) ∨ (p6 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_34 : (p3 ∨ p5) := by
          apply Or.inr
          exact assump_4
        let assump_22 := assump_2 assump_34
        apply False.elim assump_22
      case inr assump_17 =>
        have assump_35 : (p3 ∨ p5) := by
          apply Or.inr
          exact assump_4
        let assump_30 := assump_2 assump_35
        apply False.elim assump_30


variable (p4 p0 p1 p6 p3 p7 : Prop)
theorem file87_86700 : (((((p0 ∧ p3) → (p6 → False)) ∧ ((True ∧ True) ∧ (True → False))) → False) ∨ ((((p4 → False) → (True → False)) ∨ ((p6 → p6) → False)) ∨ (((p7 → p1) ∨ (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_20 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_20
        apply False.elim assump_16


variable (p6 p0 p7 p4 : Prop)
theorem file87_87274 : ((((((p7 → False) ∧ (p0 ∧ False)) → False) ∧ (((p4 ∧ p0) ∧ (True → False)) → ((p7 ∧ p4) → (True ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p7 → False) ∧ (p0 ∧ False)) → False) ∧ (((p4 ∧ p0) ∧ (True → False)) → ((p7 ∧ p4) → (True ∨ p6)))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    intro assump_16
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_16
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p6 p3 p2 p0 p4 p7 p1 : Prop)
theorem file87_88142 : ((((((True → False) ∧ (False ∧ p6)) ∧ ((p7 ∨ p4) ∧ (p6 → False))) ∧ (((p7 → False) ∨ (p3 ∨ p4)) ∨ ((p4 → False) ∨ (p0 → False)))) ∧ ((((p7 → p1) → False) ∧ ((p2 → p4) ∧ (p2 ∧ p0))) → (((p4 → False) → False) ∨ ((p3 ∧ p3) → False)))) → False) := by
  intro assump_45
  cases assump_45
  case intro assump_46 assump_47 =>
    cases assump_46
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            apply False.elim assump_56


variable (p1 p4 p3 p6 p5 p7 p2 p0 : Prop)
theorem file87_88822 : (((((p0 ∧ True) ∧ (p3 ∨ p0)) ∧ ((p6 ∨ p0) ∨ (p0 ∨ p6))) ∧ (((p5 ∧ p1) ∧ (True → False)) → False)) ∨ ((((p4 → False) → False) → ((p5 ∧ p0) → (p5 ∧ p0))) ∨ (((p3 → False) ∧ (p7 ∧ p2)) ∨ ((p5 → p3) → False)))) := by
  apply Or.inr
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    exact assump_3
  cases assump_2
  case intro assump_11 assump_12 =>
    exact assump_12


variable (p4 p6 p5 p1 : Prop)
theorem file87_89314 : ((((((True ∨ p4) ∧ (p1 → True)) → False) → (((p5 ∨ p1) → False) ∨ ((p6 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True ∨ p4) ∧ (p1 → True)) → False) → (((p5 ∨ p1) → False) ∨ ((p6 ∨ True) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      have assump_31 : ((True ∨ p4) ∧ (p1 → True)) := by
        apply And.intro
        apply Or.inl
        apply True.intro
        intro assump_15
        apply True.intro
      let assump_14 := assump_5 assump_31
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_32 : ((True ∨ p4) ∧ (p1 → True)) := by
        apply And.intro
        apply Or.inl
        apply True.intro
        intro assump_23
        apply True.intro
      let assump_22 := assump_5 assump_32
      apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p1 p5 p0 p7 p3 p6 : Prop)
theorem file87_90310 : (((((p3 → False) → (p5 → p1)) → ((True ∧ p7) ∨ (p0 → p0))) ∧ (((True → p1) → False) → False)) → ((((True → False) → (p1 → p6)) ∧ ((p7 → False) ∧ (p5 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12


variable (p3 p1 p5 p7 : Prop)
theorem file87_90776 : (((((False → False) → (False → p5)) → False) → False) ∨ ((((True → p7) ∧ (True ∨ True)) → ((p1 → False) → (p7 → p1))) → (((p3 → p5) → False) → False))) := by
  apply Or.inl
  intro assump_9
  have assump_20 : ((False → False) → (False → p5)) := by
    intro assump_13
    intro assump_14
    apply False.elim assump_14
  let assump_12 := assump_9 assump_20
  apply False.elim assump_12


variable (p1 p4 p3 p6 p0 : Prop)
theorem file87_91219 : (((((p1 ∧ p6) ∧ (p3 → False)) ∧ ((p4 ∨ p0) ∧ (p1 → False))) → False) ∧ ((((p1 → False) → (False → False)) → False) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            have assump_45 : p1 := by
              exact assump_6
            let assump_22 := assump_15 assump_45
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_46 : p1 := by
              exact assump_6
            let assump_30 := assump_15 assump_46
            apply False.elim assump_30
  intro assump_34
  have assump_47 : ((p1 → False) → (False → False)) := by
    intro assump_38
    intro assump_39
    apply False.elim assump_39
  let assump_37 := assump_34 assump_47
  apply False.elim assump_37


variable (p0 p5 p1 p4 p3 p7 : Prop)
theorem file87_92290 : (((((False → p7) → False) → False) ∨ (((True ∧ p7) ∧ (p1 → p4)) ∨ ((False ∧ False) → (p7 ∨ False)))) ∨ ((((p5 → p4) ∧ (False ∨ p1)) → ((p1 ∧ p3) → False)) → (((p4 → p0) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → p7) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p1 p3 : Prop)
theorem file87_92735 : ((((((p3 → False) ∧ (False ∧ p1)) ∧ ((p2 ∨ False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p3 → False) ∧ (False ∧ p1)) ∧ ((p2 ∨ False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p3 p1 p5 : Prop)
theorem file87_93291 : ((((((True → False) → (p1 → False)) → False) → (((p7 ∨ True) ∧ (p3 → p5)) → ((False ∧ True) → False))) → False) → False) := by
  intro assump_21
  have assump_35 : ((((True → False) → (p1 → False)) → False) → (((p7 ∨ True) ∧ (p3 → p5)) → ((False ∧ True) → False))) := by
    intro assump_25
    intro assump_26
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      apply False.elim assump_28
  let assump_24 := assump_21 assump_35
  apply False.elim assump_24


variable (p0 p3 p4 p5 p6 : Prop)
theorem file87_93838 : (((((True → False) ∧ (p6 → False)) ∨ ((False ∨ True) → False)) ∧ (((p0 ∧ p5) → (False → False)) ∧ ((p4 → p3) ∧ (False → p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_49 : True := by
              apply True.intro
            let assump_26 := assump_6 assump_49
            apply False.elim assump_26
    case inr assump_5 =>
      cases assump_3
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          have assump_50 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_45 := assump_5 assump_50
          apply False.elim assump_45


variable (p2 p6 p4 p0 p1 p7 : Prop)
theorem file87_94841 : (((((p6 ∧ True) ∧ (False → False)) ∨ ((True → p6) ∧ (p2 ∨ p7))) → (((p6 → True) → False) → False)) ∧ ((((p4 → False) → False) ∧ ((p1 ∨ p4) → (p0 ∨ p4))) → (((False ∧ p6) ∧ (p1 → False)) → ((p0 → False) ∨ (False ∨ p4))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_58 : (p6 → True) := by
          intro assump_20
          apply True.intro
        let assump_19 := assump_2 assump_58
        apply False.elim assump_19
  case inr assump_6 =>
    cases assump_6
    case intro assump_24 assump_25 =>
      cases assump_25
      case inl assump_28 =>
        have assump_59 : (p6 → True) := by
          intro assump_36
          apply True.intro
        let assump_35 := assump_2 assump_59
        apply False.elim assump_35
      case inr assump_29 =>
        have assump_60 : (p6 → True) := by
          intro assump_46
          apply True.intro
        let assump_45 := assump_2 assump_60
        apply False.elim assump_45
  intro assump_50
  intro assump_51
  cases assump_51
  case intro assump_52 assump_53 =>
    cases assump_52
    case intro assump_54 assump_55 =>
      apply False.elim assump_54


variable (p1 p3 : Prop)
theorem file87_96187 : ((((((False → p1) → False) ∧ ((True → False) ∧ (False → p3))) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False → p1) → False) ∧ ((True → False) ∧ (False → p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_25 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_25
        apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p1 p0 p7 p3 p5 p2 p4 p6 : Prop)
theorem file87_96802 : (((((False → True) ∧ (p2 ∧ p6)) ∧ ((p3 ∨ p5) ∨ (p3 ∨ p1))) ∧ (((p5 ∨ False) → (p0 ∧ p2)) → ((p7 ∧ p6) → (p4 → p4)))) ∨ ((((False → False) ∨ (False ∨ p5)) → False) → (((p5 → False) ∨ (p3 ∨ p0)) → ((True ∨ p7) ∨ (p5 ∧ p6))))) := by
  apply Or.inr
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_5 =>
    cases assump_5
    case inl assump_10 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_11 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p4 p1 p6 p5 p7 : Prop)
theorem file87_97449 : ((((((True → False) → False) ∨ ((True → False) → False)) ∨ (((p5 ∧ False) → (p1 ∧ p1)) ∨ ((p5 → False) ∨ (p7 ∨ p6)))) ∧ ((((p6 ∧ p4) → False) → ((p7 ∧ p4) → False)) ∧ (((p4 → False) ∧ (p6 → False)) ∧ ((p7 ∧ p4) ∧ (p1 ∨ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_23
                  case inl assump_30 =>
                    have assump_276 : p4 := by
                      exact assump_25
                    let assump_38 := assump_16 assump_276
                    apply False.elim assump_38
                  case inr assump_31 =>
                    have assump_277 : p4 := by
                      exact assump_31
                    let assump_48 := assump_16 assump_277
                    apply False.elim assump_48
      case inr assump_7 =>
        cases assump_3
        case intro assump_54 assump_55 =>
          cases assump_55
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              cases assump_59
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  cases assump_67
                  case inl assump_74 =>
                    have assump_278 : p4 := by
                      exact assump_69
                    let assump_82 := assump_60 assump_278
                    apply False.elim assump_82
                  case inr assump_75 =>
                    have assump_279 : p4 := by
                      exact assump_75
                    let assump_92 := assump_60 assump_279
                    apply False.elim assump_92
    case inr assump_5 =>
      cases assump_5
      case inl assump_96 =>
        cases assump_3
        case intro assump_100 assump_101 =>
          cases assump_101
          case intro assump_104 assump_105 =>
            cases assump_104
            case intro assump_106 assump_107 =>
              cases assump_105
              case intro assump_112 assump_113 =>
                cases assump_112
                case intro assump_114 assump_115 =>
                  cases assump_113
                  case inl assump_120 =>
                    have assump_280 : p4 := by
                      exact assump_115
                    let assump_128 := assump_106 assump_280
                    apply False.elim assump_128
                  case inr assump_121 =>
                    have assump_281 : p4 := by
                      exact assump_121
                    let assump_138 := assump_106 assump_281
                    apply False.elim assump_138
      case inr assump_97 =>
        cases assump_97
        case inl assump_142 =>
          cases assump_3
          case intro assump_146 assump_147 =>
            cases assump_147
            case intro assump_150 assump_151 =>
              cases assump_150
              case intro assump_152 assump_153 =>
                cases assump_151
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    cases assump_159
                    case inl assump_166 =>
                      have assump_282 : p4 := by
                        exact assump_161
                      let assump_174 := assump_152 assump_282
                      apply False.elim assump_174
                    case inr assump_167 =>
                      have assump_283 : p4 := by
                        exact assump_167
                      let assump_184 := assump_152 assump_283
                      apply False.elim assump_184
        case inr assump_143 =>
          cases assump_143
          case inl assump_188 =>
            cases assump_3
            case intro assump_192 assump_193 =>
              cases assump_193
              case intro assump_196 assump_197 =>
                cases assump_196
                case intro assump_198 assump_199 =>
                  cases assump_197
                  case intro assump_204 assump_205 =>
                    cases assump_204
                    case intro assump_206 assump_207 =>
                      cases assump_205
                      case inl assump_212 =>
                        have assump_284 : p4 := by
                          exact assump_207
                        let assump_220 := assump_198 assump_284
                        apply False.elim assump_220
                      case inr assump_213 =>
                        have assump_285 : p4 := by
                          exact assump_213
                        let assump_230 := assump_198 assump_285
                        apply False.elim assump_230
          case inr assump_189 =>
            cases assump_3
            case intro assump_236 assump_237 =>
              cases assump_237
              case intro assump_240 assump_241 =>
                cases assump_240
                case intro assump_242 assump_243 =>
                  cases assump_241
                  case intro assump_248 assump_249 =>
                    cases assump_248
                    case intro assump_250 assump_251 =>
                      cases assump_249
                      case inl assump_256 =>
                        have assump_286 : p6 := by
                          exact assump_189
                        let assump_263 := assump_243 assump_286
                        apply False.elim assump_263
                      case inr assump_257 =>
                        have assump_287 : p6 := by
                          exact assump_189
                        let assump_272 := assump_243 assump_287
                        apply False.elim assump_272


variable (p2 p5 p0 p1 p7 p3 p6 p4 : Prop)
theorem file87_103713 : (((((p5 → False) → (p4 → False)) ∧ ((p4 ∨ True) ∨ (p6 ∨ p1))) → (((p2 → False) → False) ∨ ((True ∧ p4) ∨ (p5 → p3)))) → ((((p1 ∨ False) → (p0 ∨ p6)) → ((False ∧ p2) → False)) ∨ (((p7 → False) ∨ (p1 → False)) ∧ ((p6 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p7 p2 p4 p1 p5 p0 p6 : Prop)
theorem file87_104165 : (((((p1 ∧ p6) → (p1 → p7)) ∧ ((p5 ∧ p2) ∧ (True → p5))) ∧ (((False → False) ∨ (p4 → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_27 : ((False → False) ∨ (p4 → p0)) := by
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_3 assump_27
          apply False.elim assump_20


variable (p2 p4 p1 p6 p0 p3 p5 : Prop)
theorem file87_104827 : (((((p0 → False) → False) ∧ ((p3 ∧ p1) → False)) ∨ (((p1 ∨ p0) ∨ (p4 ∧ p3)) ∧ ((p5 ∧ p0) → False))) → ((((p0 ∨ True) → (p2 → p1)) → False) → (((p6 ∨ p6) ∧ (False ∧ p5)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    case inr assump_7 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        apply False.elim assump_16


variable (p7 p0 p2 : Prop)
theorem file87_105427 : ((((((p0 ∧ p7) → (p7 → p0)) ∧ ((False ∧ p2) → False)) ∨ (((True ∨ p2) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∧ p7) → (p7 → p0)) ∧ ((False ∧ p2) → False)) ∨ (((True ∨ p2) → False) → False)) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p4 p3 p7 p0 : Prop)
theorem file87_106054 : ((((((True → False) ∨ (p7 ∧ p4)) ∧ ((p4 ∧ p0) ∧ (p3 → p5))) → (((True ∨ p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_60 : ((((True → False) ∨ (p7 ∧ p4)) ∧ ((p4 ∧ p0) ∧ (p3 → p5))) → (((True ∨ p3) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            have assump_61 : True := by
              apply True.intro
            let assump_28 := assump_11 assump_61
            apply False.elim assump_28
      case inr assump_12 =>
        cases assump_12
        case intro assump_32 assump_33 =>
          cases assump_10
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              have assump_62 : (True ∨ p3) := by
                apply Or.inl
                apply True.intro
              let assump_53 := assump_6 assump_62
              apply False.elim assump_53
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p3 p2 p5 p4 p6 p1 p0 p7 : Prop)
theorem file87_107317 : (((((p4 → p4) ∨ (p5 ∧ p0)) ∨ ((p3 → False) → False)) → (((p7 → p7) ∨ (p6 → False)) ∨ ((False → False) → (p3 ∧ p3)))) → ((((p1 ∧ p4) → (p7 ∨ p4)) → ((True ∨ p6) ∨ (False ∨ p4))) ∨ (((p6 → p3) → (True → False)) ∧ ((p2 ∧ p4) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p5 p0 p2 p1 p3 : Prop)
theorem file87_107712 : (((((p5 ∨ p2) → False) → False) → False) → ((((p3 ∨ True) ∨ (p0 ∧ p0)) → ((p2 ∨ p0) → False)) → (((p1 ∧ p2) ∧ (p0 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      have assump_29 : (((p5 ∨ p2) → False) → False) := by
        intro assump_19
        have assump_30 : (p5 ∨ p2) := by
          apply Or.inr
          exact assump_7
        let assump_22 := assump_19 assump_30
        apply False.elim assump_22
      let assump_18 := assump_1 assump_29
      apply False.elim assump_18


variable (p4 p6 p0 p5 p2 p7 : Prop)
theorem file87_108397 : ((((((p7 ∧ p0) ∧ (p0 → p0)) ∧ ((p7 → True) → False)) → (((p6 → p2) ∨ (p4 → True)) → ((p5 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_61 : ((((p7 ∧ p0) ∧ (p0 → p0)) ∧ ((p7 → True) → False)) → (((p6 → p2) ∨ (p4 → True)) → ((p5 ∧ p0) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              have assump_62 : (p7 → True) := by
                intro assump_33
                apply True.intro
              let assump_32 := assump_19 assump_62
              apply False.elim assump_32
      case inr assump_15 =>
        cases assump_5
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              have assump_63 : (p7 → True) := by
                intro assump_54
                apply True.intro
              let assump_53 := assump_40 assump_63
              apply False.elim assump_53
  let assump_4 := assump_1 assump_61
  apply False.elim assump_4


variable (p2 p3 p4 p0 p6 p5 : Prop)
theorem file87_109817 : (((((p3 ∧ False) → False) ∧ ((False ∧ p3) → False)) → (((p5 → False) ∨ (p3 ∨ False)) → ((False ∧ p4) → False))) ∨ ((((p2 → False) → False) ∨ ((p2 ∨ True) → (p6 ∧ p6))) → (((p0 ∨ p3) ∨ (p0 ∧ p0)) ∧ ((True ∨ p5) → (False → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4


variable (p3 p5 p6 p2 p1 p0 : Prop)
theorem file87_110262 : ((((((True → False) → False) → False) → False) ∧ ((((p5 ∨ p0) → (p5 ∧ True)) ∨ ((False ∧ False) → (False ∨ p6))) ∧ (((p2 → p1) → False) ∧ ((p6 ∨ p3) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_62 : True := by
                apply True.intro
              let assump_24 := assump_17 assump_62
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_63 : True := by
                apply True.intro
              let assump_32 := assump_17 assump_63
              apply False.elim assump_32
      case inr assump_9 =>
        cases assump_7
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            cases assump_42
            case inl assump_44 =>
              have assump_64 : True := by
                apply True.intro
              let assump_50 := assump_43 assump_64
              apply False.elim assump_50
            case inr assump_45 =>
              have assump_65 : True := by
                apply True.intro
              let assump_58 := assump_43 assump_65
              apply False.elim assump_58


variable (p6 p5 p4 : Prop)
theorem file87_111826 : ((((((True → False) → (p6 → p4)) → False) → (((p5 ∧ False) ∨ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True → False) → (p6 → p4)) → False) → (((p5 ∧ False) ∨ (p4 → False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      have assump_37 : ((True → False) → (p6 → p4)) := by
        intro assump_20
        intro assump_21
        have assump_38 : True := by
          apply True.intro
        let assump_26 := assump_20 assump_38
        apply False.elim assump_26
      let assump_19 := assump_5 assump_37
      apply False.elim assump_19
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p4 p6 p0 p5 p3 p2 p7 : Prop)
theorem file87_112714 : ((((((p2 → p3) ∨ (p4 → p0)) → False) ∨ (((p0 ∨ p3) ∧ (p3 → p6)) ∧ ((p4 ∧ p2) ∨ (p0 ∧ True)))) ∧ ((((p6 ∧ p3) ∧ (p4 → False)) ∧ ((p6 ∨ p5) → False)) ∧ (((p3 → p6) ∧ (p7 ∨ p5)) → ((p5 → False) → (False ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              have assump_180 : (p6 ∨ p5) := by
                apply Or.inl
                exact assump_14
              let assump_30 := assump_11 assump_180
              apply False.elim assump_30
    case inr assump_5 =>
      cases assump_5
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            cases assump_35
            case inl assump_44 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_3
                case intro assump_52 assump_53 =>
                  cases assump_52
                  case intro assump_54 assump_55 =>
                    cases assump_54
                    case intro assump_56 assump_57 =>
                      cases assump_56
                      case intro assump_58 assump_59 =>
                        have assump_181 : (p6 ∨ p5) := by
                          apply Or.inl
                          exact assump_58
                        let assump_74 := assump_55 assump_181
                        apply False.elim assump_74
            case inr assump_45 =>
              cases assump_45
              case intro assump_78 assump_79 =>
                cases assump_3
                case intro assump_84 assump_85 =>
                  cases assump_84
                  case intro assump_86 assump_87 =>
                    cases assump_86
                    case intro assump_88 assump_89 =>
                      cases assump_88
                      case intro assump_90 assump_91 =>
                        have assump_182 : (p6 ∨ p5) := by
                          apply Or.inl
                          exact assump_90
                        let assump_106 := assump_87 assump_182
                        apply False.elim assump_106
          case inr assump_39 =>
            cases assump_35
            case inl assump_114 =>
              cases assump_114
              case intro assump_116 assump_117 =>
                cases assump_3
                case intro assump_122 assump_123 =>
                  cases assump_122
                  case intro assump_124 assump_125 =>
                    cases assump_124
                    case intro assump_126 assump_127 =>
                      cases assump_126
                      case intro assump_128 assump_129 =>
                        have assump_183 : (p6 ∨ p5) := by
                          apply Or.inl
                          exact assump_128
                        let assump_144 := assump_125 assump_183
                        apply False.elim assump_144
            case inr assump_115 =>
              cases assump_115
              case intro assump_148 assump_149 =>
                cases assump_3
                case intro assump_154 assump_155 =>
                  cases assump_154
                  case intro assump_156 assump_157 =>
                    cases assump_156
                    case intro assump_158 assump_159 =>
                      cases assump_158
                      case intro assump_160 assump_161 =>
                        have assump_184 : (p6 ∨ p5) := by
                          apply Or.inl
                          exact assump_160
                        let assump_176 := assump_157 assump_184
                        apply False.elim assump_176


variable (p0 p1 p4 p2 p3 p7 p5 : Prop)
theorem file87_116782 : (((((p3 → False) → (p7 → p0)) ∨ ((p3 → False) ∧ (p5 → False))) ∧ (((p3 ∧ p2) ∨ (p4 → p4)) → ((p7 ∧ p5) → (p0 ∧ True)))) → ((((p1 ∧ p3) → (p7 ∧ True)) ∨ ((p4 → False) → (False ∨ p2))) → (((p0 ∧ False) → False) ∧ ((p7 ∧ p0) → (True ∨ p7))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_2
    case inl assump_17 =>
      cases assump_1
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          apply Or.inl
          apply True.intro
        case inr assump_24 =>
          cases assump_24
          case intro assump_29 assump_30 =>
            apply Or.inl
            apply True.intro
    case inr assump_18 =>
      cases assump_1
      case intro assump_39 assump_40 =>
        cases assump_39
        case inl assump_41 =>
          apply Or.inl
          apply True.intro
        case inr assump_42 =>
          cases assump_42
          case intro assump_47 assump_48 =>
            apply Or.inl
            apply True.intro


variable (p7 p4 p6 p3 p1 p5 : Prop)
theorem file87_118019 : ((((((p6 → False) ∧ (p4 ∧ p3)) → ((p7 ∧ p6) ∨ (False ∨ p4))) ∨ (((p3 → False) → (False ∨ p5)) ∧ ((p4 ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p6 → False) ∧ (p4 ∧ p3)) → ((p7 ∧ p6) ∨ (False ∨ p4))) ∨ (((p3 → False) → (False ∨ p5)) ∧ ((p4 ∧ p1) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply Or.inr
        exact assump_10
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p0 p2 p5 p1 p4 p3 : Prop)
theorem file87_118662 : (((((p1 ∨ p1) → (p0 ∨ True)) → False) ∧ (((p2 ∧ p3) ∧ (p3 ∧ p2)) ∧ ((p4 ∨ p5) → (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            have assump_40 : ((p1 ∨ p1) → (p0 ∨ True)) := by
              intro assump_30
              cases assump_30
              case inl assump_31 =>
                apply Or.inr
                apply True.intro
              case inr assump_32 =>
                apply Or.inr
                apply True.intro
            let assump_29 := assump_2 assump_40
            apply False.elim assump_29


variable (p2 p6 p4 p7 p1 p3 p0 p5 : Prop)
theorem file87_119559 : (((((True ∨ p2) → (p0 ∧ False)) → False) ∨ (((p4 → False) → (p6 ∨ False)) → False)) ∨ ((((False ∨ True) → False) → ((p5 → False) ∧ (p1 → p7))) ∧ (((p3 ∨ p7) ∧ (p6 → False)) → ((p2 ∨ p4) ∧ (p3 ∨ p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_10 : (True ∨ p2) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_10
  let assump_5 := And.right assump_4
  apply False.elim assump_5


variable (p6 p5 p1 p0 p3 : Prop)
theorem file87_120048 : (((((p0 → p6) ∨ (p0 → False)) ∨ ((p5 ∨ p5) → False)) ∧ (((True → False) → (False ∧ p5)) → False)) → ((((p3 ∨ True) → False) → ((p5 ∨ p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_74 : ((True → False) → (False ∧ p5)) := by
          intro assump_16
          apply And.intro
          have assump_75 : True := by
            apply True.intro
          let assump_19 := assump_16 assump_75
          apply False.elim assump_19
          have assump_76 : True := by
            apply True.intro
          let assump_25 := assump_16 assump_76
          apply False.elim assump_25
        let assump_15 := assump_6 assump_74
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_77 : ((True → False) → (False ∧ p5)) := by
          intro assump_37
          apply And.intro
          have assump_78 : True := by
            apply True.intro
          let assump_40 := assump_37 assump_78
          apply False.elim assump_40
          have assump_79 : True := by
            apply True.intro
          let assump_46 := assump_37 assump_79
          apply False.elim assump_46
        let assump_36 := assump_6 assump_77
        apply False.elim assump_36
    case inr assump_8 =>
      have assump_80 : ((True → False) → (False ∧ p5)) := by
        intro assump_58
        apply And.intro
        have assump_81 : True := by
          apply True.intro
        let assump_61 := assump_58 assump_81
        apply False.elim assump_61
        have assump_82 : True := by
          apply True.intro
        let assump_67 := assump_58 assump_82
        apply False.elim assump_67
      let assump_57 := assump_6 assump_80
      apply False.elim assump_57


variable (p2 p3 p7 p6 p0 p5 : Prop)
theorem file87_121963 : ((((((p7 ∨ p5) → False) ∧ ((p2 ∨ p0) ∧ (p3 ∨ p6))) → False) ∧ ((((p7 → False) ∧ (True ∨ p6)) → ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_37 : (((p7 → False) ∧ (True ∨ p6)) → ((True → False) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_38 : True := by
            apply True.intro
          let assump_22 := assump_10 assump_38
          apply False.elim assump_22
        case inr assump_18 =>
          have assump_39 : True := by
            apply True.intro
          let assump_30 := assump_10 assump_39
          apply False.elim assump_30
    let assump_8 := assump_3 assump_37
    apply False.elim assump_8


variable (p3 p1 p6 p0 p7 p4 p5 : Prop)
theorem file87_122884 : (((((True ∧ False) ∧ (False → False)) ∧ ((p3 ∨ False) → False)) ∧ (((p3 → p6) → (p1 ∧ p6)) ∨ ((p1 ∧ p4) → False))) ∨ ((((False ∧ p5) ∨ (True ∨ p6)) → ((True ∧ p6) → (p1 → p7))) → (((p3 ∧ p0) ∧ (p3 → False)) → ((p6 ∧ p0) ∧ (p0 ∨ p6))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_45 : p3 := by
        exact assump_5
      let assump_17 := assump_4 assump_45
      apply False.elim assump_17
  cases assump_2
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      exact assump_24
  cases assump_2
  case intro assump_33 assump_34 =>
    cases assump_33
    case intro assump_35 assump_36 =>
      apply Or.inl
      exact assump_36


variable (p5 p7 p1 p2 p0 p3 : Prop)
theorem file87_123792 : (((((p5 ∨ p3) ∧ (p1 → p3)) → ((p1 ∧ False) ∧ (True → p3))) → (((p1 ∧ False) → (False → False)) ∨ ((p0 → False) ∧ (p7 → False)))) ∨ ((((p7 ∧ p2) ∨ (p3 ∨ p5)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p7 p3 p5 p0 p1 p6 : Prop)
theorem file87_124143 : ((((((p0 → p7) → (False → p6)) ∨ ((p6 → False) → False)) → False) ∨ ((((p1 ∨ True) ∨ (p0 ∧ p3)) → ((False ∧ p6) → (False ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_30 : (((p0 → p7) → (False → p6)) ∨ ((p6 → False) → False)) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      apply False.elim assump_8
    let assump_6 := assump_2 assump_30
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_31 : (((p1 ∨ True) ∨ (p0 ∧ p3)) → ((False ∧ p6) → (False ∧ p5))) := by
      intro assump_17
      intro assump_18
      apply And.intro
      cases assump_18
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
      cases assump_18
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
    let assump_16 := assump_3 assump_31
    apply False.elim assump_16


variable (p0 p6 p4 p7 : Prop)
theorem file87_125092 : ((((((p0 ∧ p7) → (p4 → False)) ∧ ((False → p6) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 ∧ p7) → (p4 → False)) ∧ ((False → p6) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_23 : (False → p6) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p5 p1 p3 p4 : Prop)
theorem file87_125660 : (((((p1 ∧ p0) ∧ (p0 → p0)) ∧ ((p5 → False) → False)) → (((p3 → False) ∨ (p1 ∨ False)) → ((False ∨ p4) → (False → False)))) ∨ ((((p1 ∨ True) ∧ (p3 → False)) ∨ ((True ∨ p4) → False)) → False)) := by
  apply Or.inl
  intro assump_27
  intro assump_28
  intro assump_29
  intro assump_30
  apply False.elim assump_30


variable (p0 p7 p4 p6 p2 : Prop)
theorem file87_126030 : ((((((True ∧ p2) → False) → False) ∧ (((p6 → True) → (p6 → False)) → False)) ∧ ((((False → False) → (True ∨ True)) ∧ ((p2 → False) ∧ (False ∧ p4))) ∨ (((p0 ∨ False) ∧ (p2 ∨ p7)) ∧ ((p6 → p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              apply False.elim assump_20
      case inr assump_11 =>
        cases assump_11
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_26
            case inl assump_28 =>
              cases assump_27
              case inl assump_32 =>
                have assump_58 : (p6 → p6) := by
                  intro assump_39
                  exact assump_39
                let assump_38 := assump_25 assump_58
                apply False.elim assump_38
              case inr assump_33 =>
                have assump_59 : (p6 → p6) := by
                  intro assump_50
                  exact assump_50
                let assump_49 := assump_25 assump_59
                apply False.elim assump_49
            case inr assump_29 =>
              apply False.elim assump_29


variable (p2 p0 p6 : Prop)
theorem file87_127551 : (((((True → False) ∧ (True → p0)) → ((p2 → False) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → False) ∧ (True → p0)) → ((p2 → False) ∨ (p6 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_26 : True := by
        apply True.intro
      let assump_18 := assump_6 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p7 p6 p0 p2 p5 p1 p4 : Prop)
theorem file87_128129 : (((((p5 ∨ p0) ∧ (True ∨ False)) ∧ ((p6 → p5) ∧ (p3 → p2))) → False) → ((((False ∧ p7) ∧ (p4 ∨ False)) → ((p6 ∨ True) ∧ (p2 ∨ True))) ∨ (((p1 → p5) → False) ∨ ((p4 → False) → (False ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
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


