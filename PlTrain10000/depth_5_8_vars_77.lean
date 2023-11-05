variable (p5 p4 p1 p6 p7 p0 p3 : Prop)
theorem file77_47 : (((((False ∧ p6) ∨ (p7 → True)) → False) ∨ (((p0 → False) → False) ∧ ((True ∨ p7) → False))) → ((((False → False) → (False → p1)) → ((p5 ∨ True) → False)) ∨ (((p3 → False) → False) ∧ ((p4 ∨ p1) → (p6 → p4))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      have assump_76 : ((False ∧ p6) ∨ (p7 → True)) := by
        apply Or.inr
        intro assump_21
        apply True.intro
      let assump_20 := assump_2 assump_76
      apply False.elim assump_20
    case inr assump_9 =>
      have assump_77 : ((False ∧ p6) ∨ (p7 → True)) := by
        apply Or.inr
        intro assump_35
        apply True.intro
      let assump_34 := assump_2 assump_77
      apply False.elim assump_34
  case inr assump_3 =>
    cases assump_3
    case intro assump_39 assump_40 =>
      apply Or.inl
      intro assump_45
      intro assump_46
      cases assump_46
      case inl assump_47 =>
        have assump_78 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_59 := assump_40 assump_78
        apply False.elim assump_59
      case inr assump_48 =>
        have assump_79 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_72 := assump_40 assump_79
        apply False.elim assump_72


variable (p1 p6 p5 p7 p2 p4 p0 : Prop)
theorem file77_1480 : (((((p0 ∨ p7) ∧ (p6 ∨ p6)) → False) ∧ (((p2 ∧ p2) ∧ (p7 ∨ True)) → False)) → ((((p5 ∧ p2) → False) ∧ ((False ∧ p2) ∧ (p2 ∨ False))) → (((p2 ∧ p4) → (p1 ∨ True)) → ((False ∧ p6) ∧ (p7 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
  cases assump_2
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  apply And.intro
  cases assump_2
  case intro assump_30 assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        apply False.elim assump_36
  cases assump_2
  case intro assump_42 assump_43 =>
    cases assump_43
    case intro assump_46 assump_47 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        apply False.elim assump_48


variable (p0 p5 p7 p2 p6 p4 p3 : Prop)
theorem file77_2676 : (((((p4 ∧ p6) ∨ (p2 → p2)) ∨ ((p2 ∨ p5) → (p4 ∧ p0))) ∨ (((p6 ∨ p6) → False) → False)) ∨ ((((p0 → p4) ∨ (p4 ∨ p3)) → ((True → p5) ∧ (p4 ∨ p0))) → (((True ∨ p7) → False) → ((p7 ∧ p6) ∧ (p3 ∧ p2))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  exact assump_1


variable (p3 p7 p0 p1 p4 p2 : Prop)
theorem file77_3034 : (((((p3 → True) ∨ (p2 ∧ p4)) → False) → (((p0 → False) → False) → False)) ∨ ((((p4 ∧ p0) → False) → ((p4 ∨ False) → (p3 → False))) ∧ (((p7 ∨ p2) ∧ (p0 ∧ p1)) ∨ ((p3 → False) → (p4 ∧ p2))))) := by
  apply Or.inl
  intro assump_22
  intro assump_23
  have assump_33 : ((p3 → True) ∨ (p2 ∧ p4)) := by
    apply Or.inl
    intro assump_29
    apply True.intro
  let assump_28 := assump_22 assump_33
  apply False.elim assump_28


variable (p6 p3 : Prop)
theorem file77_3506 : ((((((p3 → False) → (p3 → False)) → ((p6 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p3 → False) → (p3 → False)) → ((p6 ∨ True) → False)) → False) := by
    intro assump_5
    have assump_27 : ((p3 → False) → (p3 → False)) := by
      intro assump_9
      intro assump_10
      have assump_28 : p3 := by
        exact assump_10
      let assump_15 := assump_9 assump_28
      apply False.elim assump_15
    let assump_8 := assump_5 assump_27
    have assump_29 : (p6 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_19 := assump_8 assump_29
    apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p2 p4 p1 p3 p7 : Prop)
theorem file77_4272 : (((((p4 → p4) → False) ∧ ((False ∧ p7) → False)) → False) ∨ ((((p5 → False) → (p1 → p4)) → ((False ∧ p2) → False)) ∧ (((p1 → p4) → (p1 → False)) ∨ ((p3 → p7) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (p4 → p4) := by
      intro assump_10
      exact assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p6 p3 p7 p0 p4 p2 : Prop)
theorem file77_4748 : ((((((False → p7) → False) → False) ∨ (((p4 ∧ p3) ∧ (p2 → p3)) ∧ ((p0 ∨ p6) ∨ (p7 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p7) → False) → False) ∨ (((p4 ∧ p3) ∧ (p2 → p3)) ∧ ((p0 ∨ p6) ∨ (p7 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → p7) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p1 p5 p7 p4 p2 : Prop)
theorem file77_5321 : (((((p2 → True) ∨ (p5 ∧ True)) → False) → False) ∨ ((((True → False) ∨ (p2 → False)) ∧ ((p2 → p1) ∨ (False ∨ p4))) → (((p5 ∨ p5) ∧ (p7 ∨ p4)) → ((p6 → False) ∧ (p1 → True))))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p2 → True) ∨ (p5 ∧ True)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p1 p4 p6 p3 p0 : Prop)
theorem file77_5768 : (((((False ∨ p0) ∧ (True ∧ p6)) ∧ ((p4 → p4) → False)) → (((p1 → p4) → False) → False)) ∨ ((((p3 → False) → (p6 → False)) ∨ ((p3 → False) → (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        apply False.elim assump_13
      case inr assump_14 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          have assump_34 : (p4 → p4) := by
            intro assump_28
            exact assump_28
          let assump_27 := assump_10 assump_34
          apply False.elim assump_27


variable (p4 p7 p2 p5 p6 p3 p1 : Prop)
theorem file77_6522 : ((((((p3 ∨ p4) → (p1 → p7)) → False) ∧ (((True → False) ∨ (p7 ∧ p7)) ∨ ((p2 → False) → False))) ∧ ((((p7 ∨ p1) → (p3 → False)) ∧ ((p5 ∧ False) ∧ (p6 ∨ p2))) ∧ (((p2 → False) ∨ (p3 ∧ False)) → ((p3 ∨ False) ∧ (p1 → p5))))) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_21
      case inl assump_24 =>
        cases assump_24
        case inl assump_26 =>
          cases assump_19
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_33
              case intro assump_36 assump_37 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  apply False.elim assump_39
        case inr assump_27 =>
          cases assump_27
          case intro assump_44 assump_45 =>
            cases assump_19
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_53
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_59
      case inr assump_25 =>
        cases assump_19
        case intro assump_66 assump_67 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_69
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                apply False.elim assump_75


variable (p3 p2 p4 p5 p6 p0 p7 : Prop)
theorem file77_8231 : ((((((p4 ∧ p0) → False) → ((p0 ∨ p0) → False)) → (((p7 ∨ True) → (p6 → p6)) ∨ ((p3 ∨ p5) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p4 ∧ p0) → False) → ((p0 ∨ p0) → False)) → (((p7 ∨ True) → (p6 → p6)) ∨ ((p3 ∨ p5) ∧ (p2 → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case inl assump_12 =>
      exact assump_9
    case inr assump_13 =>
      exact assump_9
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p2 p3 p0 p1 p5 p4 p6 : Prop)
theorem file77_8827 : (((((False ∧ True) ∧ (True → False)) → ((False ∨ p7) → (p7 ∨ p6))) → False) → ((((p0 ∧ p2) → (p1 → False)) → ((p3 → False) ∨ (False ∧ p5))) → (((p4 → p2) ∧ (p7 → p1)) ∨ ((p4 ∧ p3) ∧ (p1 → p6))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply And.intro
  intro assump_7
  have assump_51 : (((False ∧ True) ∧ (True → False)) → ((False ∨ p7) → (p7 ∨ p6))) := by
    intro assump_12
    intro assump_13
    cases assump_13
    case inl assump_14 =>
      apply False.elim assump_14
    case inr assump_15 =>
      cases assump_12
      case intro assump_20 assump_21 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  let assump_11 := assump_1 assump_51
  apply False.elim assump_11
  intro assump_29
  have assump_52 : (((False ∧ True) ∧ (True → False)) → ((False ∨ p7) → (p7 ∨ p6))) := by
    intro assump_34
    intro assump_35
    cases assump_35
    case inl assump_36 =>
      apply False.elim assump_36
    case inr assump_37 =>
      cases assump_34
      case intro assump_42 assump_43 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply False.elim assump_44
  let assump_33 := assump_1 assump_52
  apply False.elim assump_33


variable (p4 p0 p3 p7 p5 p2 p1 p6 : Prop)
theorem file77_10131 : (((((p4 → p5) → (p1 → p3)) ∧ ((p4 → p7) ∧ (True → False))) ∧ (((p2 ∨ p3) ∧ (p7 ∨ True)) ∧ ((p6 ∧ p7) → False))) → ((((p7 ∧ p7) → (p0 → p0)) ∨ ((p3 → p1) ∧ (p4 ∨ p2))) → (((p2 ∧ True) → False) ∨ ((p4 ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          cases assump_8
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_22
                case inl assump_27 =>
                  apply Or.inl
                  intro assump_33
                  cases assump_33
                  case intro assump_34 assump_35 =>
                    have assump_317 : True := by
                      apply True.intro
                    let assump_44 := assump_14 assump_317
                    apply False.elim assump_44
                case inr assump_28 =>
                  apply Or.inl
                  intro assump_52
                  cases assump_52
                  case intro assump_53 assump_54 =>
                    have assump_318 : True := by
                      apply True.intro
                    let assump_62 := assump_14 assump_318
                    apply False.elim assump_62
              case inr assump_24 =>
                cases assump_22
                case inl assump_68 =>
                  apply Or.inl
                  intro assump_74
                  cases assump_74
                  case intro assump_75 assump_76 =>
                    have assump_319 : True := by
                      apply True.intro
                    let assump_85 := assump_14 assump_319
                    apply False.elim assump_85
                case inr assump_69 =>
                  apply Or.inl
                  intro assump_93
                  cases assump_93
                  case intro assump_94 assump_95 =>
                    have assump_320 : True := by
                      apply True.intro
                    let assump_103 := assump_14 assump_320
                    apply False.elim assump_103
  case inr assump_4 =>
    cases assump_4
    case intro assump_107 assump_108 =>
      cases assump_108
      case inl assump_111 =>
        cases assump_1
        case intro assump_115 assump_116 =>
          cases assump_115
          case intro assump_117 assump_118 =>
            cases assump_118
            case intro assump_121 assump_122 =>
              cases assump_116
              case intro assump_127 assump_128 =>
                cases assump_127
                case intro assump_129 assump_130 =>
                  cases assump_129
                  case inl assump_131 =>
                    cases assump_130
                    case inl assump_135 =>
                      apply Or.inl
                      intro assump_141
                      cases assump_141
                      case intro assump_142 assump_143 =>
                        have assump_321 : True := by
                          apply True.intro
                        let assump_152 := assump_122 assump_321
                        apply False.elim assump_152
                    case inr assump_136 =>
                      apply Or.inl
                      intro assump_160
                      cases assump_160
                      case intro assump_161 assump_162 =>
                        have assump_322 : True := by
                          apply True.intro
                        let assump_170 := assump_122 assump_322
                        apply False.elim assump_170
                  case inr assump_132 =>
                    cases assump_130
                    case inl assump_176 =>
                      apply Or.inl
                      intro assump_182
                      cases assump_182
                      case intro assump_183 assump_184 =>
                        have assump_323 : True := by
                          apply True.intro
                        let assump_193 := assump_122 assump_323
                        apply False.elim assump_193
                    case inr assump_177 =>
                      apply Or.inl
                      intro assump_201
                      cases assump_201
                      case intro assump_202 assump_203 =>
                        have assump_324 : True := by
                          apply True.intro
                        let assump_211 := assump_122 assump_324
                        apply False.elim assump_211
      case inr assump_112 =>
        cases assump_1
        case intro assump_217 assump_218 =>
          cases assump_217
          case intro assump_219 assump_220 =>
            cases assump_220
            case intro assump_223 assump_224 =>
              cases assump_218
              case intro assump_229 assump_230 =>
                cases assump_229
                case intro assump_231 assump_232 =>
                  cases assump_231
                  case inl assump_233 =>
                    cases assump_232
                    case inl assump_237 =>
                      apply Or.inl
                      intro assump_243
                      cases assump_243
                      case intro assump_244 assump_245 =>
                        have assump_325 : True := by
                          apply True.intro
                        let assump_254 := assump_224 assump_325
                        apply False.elim assump_254
                    case inr assump_238 =>
                      apply Or.inl
                      intro assump_262
                      cases assump_262
                      case intro assump_263 assump_264 =>
                        have assump_326 : True := by
                          apply True.intro
                        let assump_272 := assump_224 assump_326
                        apply False.elim assump_272
                  case inr assump_234 =>
                    cases assump_232
                    case inl assump_278 =>
                      apply Or.inl
                      intro assump_284
                      cases assump_284
                      case intro assump_285 assump_286 =>
                        have assump_327 : True := by
                          apply True.intro
                        let assump_295 := assump_224 assump_327
                        apply False.elim assump_295
                    case inr assump_279 =>
                      apply Or.inl
                      intro assump_303
                      cases assump_303
                      case intro assump_304 assump_305 =>
                        have assump_328 : True := by
                          apply True.intro
                        let assump_313 := assump_224 assump_328
                        apply False.elim assump_313


variable (p4 p1 p0 p2 p7 : Prop)
theorem file77_17226 : ((((((p4 ∨ p0) → (p4 → False)) → ((p1 ∨ False) ∧ (p1 ∧ p2))) → (((p4 ∧ p4) ∧ (p4 ∧ True)) → ((p7 ∨ p4) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p4 ∨ p0) → (p4 → False)) → ((p1 ∨ False) ∧ (p1 ∧ p2))) → (((p4 ∧ p4) ∧ (p4 ∧ True)) → ((p7 ∨ p4) ∨ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply Or.inr
          exact assump_15
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p0 p5 p3 p6 p7 p2 : Prop)
theorem file77_17950 : (((((True ∧ True) → (True ∨ True)) ∨ ((p3 ∨ p6) ∧ (p2 → p2))) ∧ (((p3 ∧ p5) ∨ (p1 → False)) → ((p7 ∨ p6) ∨ (False → False)))) ∨ ((((p5 ∧ False) ∨ (p0 → False)) → ((False → False) → False)) ∧ (((False → False) → False) ∧ ((p2 → p3) ∧ (False → True))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply True.intro
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply Or.inr
      intro assump_17
      apply False.elim assump_17
  case inr assump_10 =>
    apply Or.inr
    intro assump_22
    apply False.elim assump_22


variable (p3 p1 p5 p6 p0 p4 p2 : Prop)
theorem file77_18705 : (((((p1 → False) → (True ∨ p6)) → False) → (((p3 → False) ∧ (p4 → True)) ∨ ((p2 → p5) ∧ (p4 → p3)))) ∨ ((((p4 ∨ p1) ∨ (p6 ∧ p4)) ∨ ((p1 ∨ p0) ∧ (p6 → False))) ∧ (((p2 ∧ p4) ∨ (True → False)) ∧ ((p2 → False) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_16 : ((p1 → False) → (True ∨ p6)) := by
    intro assump_9
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_16
  apply False.elim assump_8
  intro assump_15
  apply True.intro


variable (p5 p6 p7 p3 p2 p1 p4 p0 : Prop)
theorem file77_19298 : (((((False → False) ∨ (True → p4)) ∧ ((p1 → p5) → False)) ∧ (((p5 ∧ p1) ∨ (True ∨ p1)) ∨ ((p0 ∧ p3) ∧ (p5 ∨ p6)))) → ((((p1 → p5) → (p7 → False)) ∨ ((p4 → False) ∧ (p6 ∨ p2))) → (((True ∨ p6) ∨ (True ∧ p6)) ∨ ((p0 ∧ p2) ∨ (p6 ∨ p2))))) := by
  intro assump_17
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_17
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case inl assump_27 =>
          cases assump_24
          case inl assump_33 =>
            cases assump_33
            case inl assump_35 =>
              cases assump_35
              case intro assump_37 assump_38 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
            case inr assump_36 =>
              cases assump_36
              case inl assump_43 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_44 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_34 =>
            cases assump_34
            case intro assump_49 assump_50 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                cases assump_50
                case inl assump_57 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_58 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
        case inr assump_28 =>
          cases assump_24
          case inl assump_67 =>
            cases assump_67
            case inl assump_69 =>
              cases assump_69
              case intro assump_71 assump_72 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
            case inr assump_70 =>
              cases assump_70
              case inl assump_77 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_78 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
          case inr assump_68 =>
            cases assump_68
            case intro assump_83 assump_84 =>
              cases assump_83
              case intro assump_85 assump_86 =>
                cases assump_84
                case inl assump_91 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                case inr assump_92 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
  case inr assump_20 =>
    cases assump_20
    case intro assump_97 assump_98 =>
      cases assump_98
      case inl assump_101 =>
        cases assump_17
        case intro assump_105 assump_106 =>
          cases assump_105
          case intro assump_107 assump_108 =>
            cases assump_107
            case inl assump_109 =>
              cases assump_106
              case inl assump_115 =>
                cases assump_115
                case inl assump_117 =>
                  cases assump_117
                  case intro assump_119 assump_120 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_118 =>
                  cases assump_118
                  case inl assump_125 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_126 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
              case inr assump_116 =>
                cases assump_116
                case intro assump_131 assump_132 =>
                  cases assump_131
                  case intro assump_133 assump_134 =>
                    cases assump_132
                    case inl assump_139 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    case inr assump_140 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
            case inr assump_110 =>
              cases assump_106
              case inl assump_149 =>
                cases assump_149
                case inl assump_151 =>
                  cases assump_151
                  case intro assump_153 assump_154 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_152 =>
                  cases assump_152
                  case inl assump_159 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_160 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
              case inr assump_150 =>
                cases assump_150
                case intro assump_165 assump_166 =>
                  cases assump_165
                  case intro assump_167 assump_168 =>
                    cases assump_166
                    case inl assump_173 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    case inr assump_174 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
      case inr assump_102 =>
        cases assump_17
        case intro assump_181 assump_182 =>
          cases assump_181
          case intro assump_183 assump_184 =>
            cases assump_183
            case inl assump_185 =>
              cases assump_182
              case inl assump_191 =>
                cases assump_191
                case inl assump_193 =>
                  cases assump_193
                  case intro assump_195 assump_196 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_194 =>
                  cases assump_194
                  case inl assump_201 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_202 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
              case inr assump_192 =>
                cases assump_192
                case intro assump_207 assump_208 =>
                  cases assump_207
                  case intro assump_209 assump_210 =>
                    cases assump_208
                    case inl assump_215 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    case inr assump_216 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
            case inr assump_186 =>
              cases assump_182
              case inl assump_225 =>
                cases assump_225
                case inl assump_227 =>
                  cases assump_227
                  case intro assump_229 assump_230 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_228 =>
                  cases assump_228
                  case inl assump_235 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_236 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
              case inr assump_226 =>
                cases assump_226
                case intro assump_241 assump_242 =>
                  cases assump_241
                  case intro assump_243 assump_244 =>
                    cases assump_242
                    case inl assump_249 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    case inr assump_250 =>
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      apply True.intro


variable (p2 p4 p7 p0 p3 p6 p5 p1 : Prop)
theorem file77_28674 : (((((p3 ∨ p5) ∨ (p1 ∨ p3)) → ((p0 ∧ True) → (p3 → p0))) ∨ (((p1 → False) ∨ (p6 ∧ p2)) → False)) ∨ ((((p2 ∨ p2) ∨ (p3 ∧ p7)) → False) ∧ (((False → False) ∧ (p0 → False)) → ((p4 ∧ p1) ∨ (p4 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        exact assump_6
      case inr assump_15 =>
        exact assump_6
    case inr assump_13 =>
      cases assump_13
      case inl assump_20 =>
        exact assump_6
      case inr assump_21 =>
        exact assump_6


variable (p2 p5 p7 p3 p6 p1 p4 p0 : Prop)
theorem file77_29395 : (((((p1 ∨ p0) ∧ (p2 ∨ False)) → ((p3 → p2) ∧ (p5 ∨ p4))) ∨ (((p0 ∨ False) ∧ (p6 ∧ p4)) ∧ ((p0 → p4) → False))) → ((((False ∧ p3) → (True → False)) ∧ ((False → False) ∧ (p1 ∨ True))) ∨ (((p3 → p7) ∨ (False → False)) ∨ ((True ∧ p4) → (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    apply And.intro
    intro assump_14
    apply False.elim assump_14
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_20
          case intro assump_25 assump_26 =>
            apply Or.inl
            apply And.intro
            intro assump_33
            intro assump_34
            cases assump_33
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
            apply And.intro
            intro assump_41
            apply False.elim assump_41
            apply Or.inr
            apply True.intro
        case inr assump_22 =>
          apply False.elim assump_22


variable (p4 p5 p3 p7 p1 p0 : Prop)
theorem file77_30747 : ((((((p5 → p1) ∧ (p4 ∧ p1)) → ((False → p0) ∨ (p1 → True))) ∨ (((True → False) → (p0 → False)) ∨ ((p7 → p3) ∧ (p0 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 → p1) ∧ (p4 ∧ p1)) → ((False → p0) ∨ (p1 → True))) ∨ (((True → False) → (p0 → False)) ∨ ((p7 → p3) ∧ (p0 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        apply False.elim assump_16
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p5 p4 p3 p6 p1 : Prop)
theorem file77_31414 : ((((((True ∨ p4) → False) ∧ ((p0 ∧ p3) ∨ (p4 → p1))) ∨ (((False → False) → (p0 → p3)) ∧ ((False ∧ p6) ∨ (p5 ∨ p0)))) ∧ ((((p1 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((p0 ∧ p5) → (p1 ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_88 : (((p1 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((p0 ∧ p5) → (p1 ∨ p0))) := by
              apply Or.inr
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                apply Or.inr
                exact assump_22
            let assump_20 := assump_3 assump_88
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_89 : (((p1 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((p0 ∧ p5) → (p1 ∨ p0))) := by
            apply Or.inr
            intro assump_36
            cases assump_36
            case intro assump_37 assump_38 =>
              apply Or.inr
              exact assump_37
          let assump_35 := assump_3 assump_89
          apply False.elim assump_35
    case inr assump_5 =>
      cases assump_5
      case intro assump_46 assump_47 =>
        cases assump_47
        case inl assump_50 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            apply False.elim assump_52
        case inr assump_51 =>
          cases assump_51
          case inl assump_56 =>
            have assump_90 : (((p1 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((p0 ∧ p5) → (p1 ∨ p0))) := by
              apply Or.inr
              intro assump_63
              cases assump_63
              case intro assump_64 assump_65 =>
                apply Or.inr
                exact assump_64
            let assump_62 := assump_3 assump_90
            apply False.elim assump_62
          case inr assump_57 =>
            have assump_91 : (((p1 ∨ p1) ∨ (p3 ∧ p4)) ∨ ((p0 ∧ p5) → (p1 ∨ p0))) := by
              apply Or.inr
              intro assump_78
              cases assump_78
              case intro assump_79 assump_80 =>
                apply Or.inr
                exact assump_79
            let assump_77 := assump_3 assump_91
            apply False.elim assump_77


variable (p3 p1 : Prop)
theorem file77_33814 : ((((((p3 → p3) → False) ∧ ((True ∨ p1) ∨ (True → False))) → (((p1 → True) → False) → False)) → False) → False) := by
  intro assump_12
  have assump_56 : ((((p3 → p3) → False) ∧ ((True ∨ p1) ∨ (True → False))) → (((p1 → True) → False) → False)) := by
    intro assump_16
    intro assump_17
    cases assump_16
    case intro assump_20 assump_21 =>
      cases assump_21
      case inl assump_24 =>
        cases assump_24
        case inl assump_26 =>
          have assump_57 : (p3 → p3) := by
            intro assump_31
            exact assump_31
          let assump_30 := assump_20 assump_57
          apply False.elim assump_30
        case inr assump_27 =>
          have assump_58 : (p3 → p3) := by
            intro assump_41
            exact assump_41
          let assump_40 := assump_20 assump_58
          apply False.elim assump_40
      case inr assump_25 =>
        have assump_59 : True := by
          apply True.intro
        let assump_49 := assump_25 assump_59
        apply False.elim assump_49
  let assump_15 := assump_12 assump_56
  apply False.elim assump_15


variable (p2 p6 p5 p7 p1 p0 p3 : Prop)
theorem file77_34965 : (((((True ∧ p0) ∨ (p2 → False)) ∧ ((p3 → False) ∧ (p3 → True))) → False) → ((((p7 ∨ True) ∧ (p7 ∨ True)) ∨ ((p7 → False) ∧ (p5 → False))) ∨ (((p1 ∨ p6) ∧ (p7 → p0)) → ((False ∨ p3) → (p3 → p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply True.intro
  apply Or.inr
  apply True.intro


variable (p1 p6 p5 p7 p2 p4 : Prop)
theorem file77_35361 : ((((((p6 → False) ∧ (p6 → p5)) → ((p4 ∨ p4) ∨ (False → True))) → False) ∧ ((((p7 ∧ False) ∧ (p2 → p5)) → ((p4 → p7) → False)) ∨ (((False ∧ p1) → False) ∨ ((p4 ∧ p2) → (False ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_55 : (((p6 → False) ∧ (p6 → p5)) → ((p4 ∨ p4) ∨ (False → True))) := by
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply Or.inr
          intro assump_19
          apply True.intro
      let assump_11 := assump_2 assump_55
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_23 =>
        have assump_56 : (((p6 → False) ∧ (p6 → p5)) → ((p4 ∨ p4) ∨ (False → True))) := by
          intro assump_29
          cases assump_29
          case intro assump_30 assump_31 =>
            apply Or.inr
            intro assump_36
            apply True.intro
        let assump_28 := assump_2 assump_56
        apply False.elim assump_28
      case inr assump_24 =>
        have assump_57 : (((p6 → False) ∧ (p6 → p5)) → ((p4 ∨ p4) ∨ (False → True))) := by
          intro assump_44
          cases assump_44
          case intro assump_45 assump_46 =>
            apply Or.inr
            intro assump_51
            apply True.intro
        let assump_43 := assump_2 assump_57
        apply False.elim assump_43


variable (p6 p4 p7 p1 p0 p2 p3 : Prop)
theorem file77_36863 : ((((((p6 → p0) ∧ (p6 → p4)) ∨ ((p0 → p0) ∧ (p3 → False))) → (((p1 ∧ p4) → False) → ((p7 ∨ p1) ∨ (p4 ∧ False)))) ∧ ((((False ∨ p2) ∧ (False ∧ p1)) ∧ ((p7 ∨ p0) → (p4 ∨ True))) ∧ (((p7 → True) ∧ (False ∧ p4)) → ((p6 → p7) → False)))) → False) := by
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
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p5 p7 p1 p6 : Prop)
theorem file77_37655 : ((((((p1 → False) → (p6 → False)) → ((p5 ∨ p1) ∨ (p6 → p6))) ∧ (((p1 → False) → False) ∨ ((p7 → p1) → False))) ∧ ((((p5 → True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_42 : (((p5 → True) → False) → False) := by
          intro assump_15
          have assump_43 : (p5 → True) := by
            intro assump_19
            apply True.intro
          let assump_18 := assump_15 assump_43
          apply False.elim assump_18
        let assump_14 := assump_3 assump_42
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_44 : (((p5 → True) → False) → False) := by
          intro assump_31
          have assump_45 : (p5 → True) := by
            intro assump_35
            apply True.intro
          let assump_34 := assump_31 assump_45
          apply False.elim assump_34
        let assump_30 := assump_3 assump_44
        apply False.elim assump_30


variable (p6 p0 p1 p7 p4 p5 p2 : Prop)
theorem file77_38795 : (((((False → p5) → False) ∧ ((p4 ∧ p1) → False)) → False) ∨ ((((p0 ∨ p0) ∧ (p2 ∨ p6)) → ((p0 ∨ p7) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (False → p5) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p5 p4 p0 p2 p6 p3 : Prop)
theorem file77_39227 : (((((True ∧ p4) ∧ (p5 ∨ p0)) ∧ ((p3 ∨ False) ∧ (p3 → False))) → False) ∨ ((((p4 → False) → False) → False) ∨ (((p2 ∧ False) → (p5 ∧ p6)) ∨ ((p5 → False) → False)))) := by
  apply Or.inl
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_21
        case inl assump_28 =>
          cases assump_19
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              have assump_62 : p3 := by
                exact assump_34
              let assump_40 := assump_33 assump_62
              apply False.elim assump_40
            case inr assump_35 =>
              apply False.elim assump_35
        case inr assump_29 =>
          cases assump_19
          case intro assump_48 assump_49 =>
            cases assump_48
            case inl assump_50 =>
              have assump_63 : p3 := by
                exact assump_50
              let assump_56 := assump_49 assump_63
              apply False.elim assump_56
            case inr assump_51 =>
              apply False.elim assump_51


variable (p6 p2 p5 p3 p0 p7 : Prop)
theorem file77_40491 : (((((p0 → p6) ∧ (p0 ∨ False)) → ((True → False) → False)) ∨ (((p7 ∨ True) ∨ (p3 → False)) → ((p2 → False) → (p5 → False)))) ∨ ((((p7 → False) → False) ∧ ((p6 ∨ p0) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      have assump_22 : True := by
        apply True.intro
      let assump_16 := assump_2 assump_22
      apply False.elim assump_16
    case inr assump_10 =>
      apply False.elim assump_10


variable (p2 p7 p5 p1 p4 : Prop)
theorem file77_41090 : (((((p2 → False) → (p5 ∧ p4)) → ((p1 → False) ∨ (p7 ∧ False))) → (((p5 ∧ False) ∧ (p2 ∧ p1)) → ((p4 → False) → False))) ∨ ((((p2 → False) → False) → False) ∧ (((p7 ∧ p7) ∧ (p2 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply False.elim assump_9


variable (p7 p3 p1 p0 p5 p2 p6 : Prop)
theorem file77_41560 : (((((False ∨ True) ∨ (True ∨ False)) → False) → (((p6 → p5) → (p7 → False)) → ((p6 ∧ p7) ∧ (p3 → p5)))) ∨ ((((False → False) → (p3 → False)) ∧ ((p0 ∧ False) → False)) ∨ (((p2 ∧ True) → (p7 ∨ p1)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  have assump_30 : ((False ∨ True) ∨ (True ∨ False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_30
  apply False.elim assump_7
  have assump_31 : ((False ∨ True) ∨ (True ∨ False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_15 := assump_1 assump_31
  apply False.elim assump_15
  intro assump_19
  have assump_32 : ((False ∨ True) ∨ (True ∨ False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_26 := assump_1 assump_32
  apply False.elim assump_26


variable (p5 p1 p2 p3 p7 p4 : Prop)
theorem file77_42477 : (((((False → True) ∧ (p7 ∨ p1)) ∨ ((True ∨ p3) ∨ (p2 ∧ p4))) ∨ (((p3 ∧ p5) → (p7 → p2)) → ((p3 → p2) → False))) ∨ ((((False → False) → False) ∧ ((p1 ∧ p7) → False)) → (((p5 ∧ p1) → False) → ((p3 ∧ p5) ∨ (p7 → p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p1 p4 p0 p2 p3 p5 p7 p6 : Prop)
theorem file77_42860 : ((((((p4 → False) ∧ (p6 → p4)) → ((p0 → p3) ∨ (p4 → False))) ∨ (((p5 ∧ p6) ∧ (True ∧ p1)) → ((p1 → p7) → False))) ∧ ((((p4 → False) ∧ (p4 → False)) → ((p2 ∨ p5) ∧ (True → False))) ∧ (((p2 → p3) ∧ (True → False)) ∧ ((False ∧ p7) ∧ (p6 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_22
    case inr assump_5 =>
      cases assump_3
      case intro assump_28 assump_29 =>
        cases assump_29
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            cases assump_33
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                apply False.elim assump_42


variable (p6 p7 p1 p4 p5 : Prop)
theorem file77_44094 : (((((p7 ∨ p5) → (True ∨ p6)) → False) ∧ (((p1 ∨ p5) → False) ∨ ((p4 → False) ∨ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_44 : ((p7 ∨ p5) → (True ∨ p6)) := by
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          apply Or.inl
          apply True.intro
        case inr assump_14 =>
          apply Or.inl
          apply True.intro
      let assump_11 := assump_2 assump_44
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_22 =>
        have assump_45 : ((p7 ∨ p5) → (True ∨ p6)) := by
          intro assump_28
          cases assump_28
          case inl assump_29 =>
            apply Or.inl
            apply True.intro
          case inr assump_30 =>
            apply Or.inl
            apply True.intro
        let assump_27 := assump_2 assump_45
        apply False.elim assump_27
      case inr assump_23 =>
        have assump_46 : True := by
          apply True.intro
        let assump_40 := assump_23 assump_46
        apply False.elim assump_40


variable (p4 p5 p2 p1 p7 p6 p3 : Prop)
theorem file77_45324 : (((((p5 ∧ p1) ∧ (p3 ∨ p5)) ∧ ((p3 ∧ p6) → False)) ∨ (((False → p2) ∧ (False → False)) ∨ ((False ∨ p2) ∨ (False ∨ False)))) ∨ ((((p4 ∨ True) ∧ (p2 ∨ False)) → False) → (((False → False) → False) ∧ ((p2 ∨ p2) ∨ (p7 → False))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply And.intro
  intro assump_11
  apply False.elim assump_11
  intro assump_14
  apply False.elim assump_14


variable (p5 p0 p4 p1 p7 : Prop)
theorem file77_45770 : (((((p5 ∧ p4) ∨ (p5 → p5)) → False) ∨ (((True → False) → False) → False)) → ((((False → p5) ∨ (p7 ∨ p1)) ∧ ((True → False) → False)) ∨ (((p0 → False) → (False → True)) ∨ ((p0 → p1) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    have assump_28 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_28
    apply False.elim assump_12
  case inr assump_3 =>
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_18
    apply False.elim assump_18
    intro assump_21
    have assump_29 : True := by
      apply True.intro
    let assump_24 := assump_21 assump_29
    apply False.elim assump_24


variable (p2 p7 p0 p4 p5 p3 p1 p6 : Prop)
theorem file77_46615 : ((((((p4 ∧ p5) ∨ (p3 → p3)) ∧ ((p3 → p0) ∧ (p0 → False))) ∧ (((p0 ∧ False) → (p1 ∧ p2)) → False)) ∧ ((((False ∧ p5) → False) → ((p7 ∧ p5) ∧ (False → p1))) ∧ (((p5 ∨ p7) ∨ (p3 ∧ p1)) → ((False → p6) → (p6 ∧ p5))))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_16
            case intro assump_25 assump_26 =>
              cases assump_12
              case intro assump_33 assump_34 =>
                have assump_120 : ((p0 ∧ False) → (p1 ∧ p2)) := by
                  intro assump_59
                  apply And.intro
                  cases assump_59
                  case intro assump_60 assump_61 =>
                    apply False.elim assump_61
                  cases assump_59
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_67
                let assump_58 := assump_14 assump_120
                apply False.elim assump_58
        case inr assump_18 =>
          cases assump_16
          case intro assump_77 assump_78 =>
            cases assump_12
            case intro assump_85 assump_86 =>
              have assump_121 : ((p0 ∧ False) → (p1 ∧ p2)) := by
                intro assump_104
                apply And.intro
                cases assump_104
                case intro assump_105 assump_106 =>
                  apply False.elim assump_106
                cases assump_104
                case intro assump_111 assump_112 =>
                  apply False.elim assump_112
              let assump_103 := assump_14 assump_121
              apply False.elim assump_103


variable (p5 p1 p4 p3 p0 p7 : Prop)
theorem file77_48531 : (((((False ∧ p4) ∧ (p7 ∧ False)) → ((p1 ∧ p0) ∧ (p4 → False))) → False) → ((((p0 → p3) → False) → False) → (((p5 → False) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_36 : (((False ∧ p4) ∧ (p7 ∧ False)) → ((p1 ∧ p0) ∧ (p4 → False))) := by
    intro assump_11
    apply And.intro
    apply And.intro
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    cases assump_11
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_20
    intro assump_24
    cases assump_11
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
  let assump_10 := assump_1 assump_36
  apply False.elim assump_10


variable (p7 p5 p6 p4 p2 : Prop)
theorem file77_49485 : ((((((p5 ∨ p5) → (p6 → True)) ∨ ((p6 → False) → False)) → (((True → False) ∨ (p4 → p2)) ∨ ((p5 ∨ p6) ∨ (p6 → False)))) ∧ ((((True → False) ∨ (True → False)) → False) → (((p6 → p6) → False) ∧ ((p7 → False) ∧ (p7 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : (((True → False) ∨ (True → False)) → False) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        have assump_33 : True := by
          apply True.intro
        let assump_14 := assump_10 assump_33
        apply False.elim assump_14
      case inr assump_11 =>
        have assump_34 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_34
        apply False.elim assump_20
    let assump_8 := assump_3 assump_32
    let assump_24 := And.left assump_8
    have assump_35 : (p6 → p6) := by
      intro assump_26
      exact assump_26
    let assump_25 := assump_24 assump_35
    apply False.elim assump_25


variable (p3 p0 p6 p1 p2 p5 : Prop)
theorem file77_50535 : (((((p1 → False) ∧ (True ∧ False)) → False) → False) → ((((p5 → p1) ∧ (p0 → p6)) → False) → (((p6 ∧ p2) → False) ∧ ((True ∨ p3) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_74 : (((p1 → False) ∧ (True ∧ False)) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
    let assump_14 := assump_1 assump_74
    apply False.elim assump_14
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    have assump_75 : (((p1 → False) ∧ (True ∧ False)) → False) := by
      intro assump_39
      cases assump_39
      case intro assump_40 assump_41 =>
        cases assump_41
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
    let assump_38 := assump_1 assump_75
    apply False.elim assump_38
  case inr assump_31 =>
    have assump_76 : (((p1 → False) ∧ (True ∧ False)) → False) := by
      intro assump_60
      cases assump_60
      case intro assump_61 assump_62 =>
        cases assump_62
        case intro assump_65 assump_66 =>
          apply False.elim assump_66
    let assump_59 := assump_1 assump_76
    apply False.elim assump_59


variable (p3 p2 p5 p6 : Prop)
theorem file77_51920 : (((((True ∨ False) ∧ (False ∧ p5)) → ((p5 ∧ p2) ∧ (p6 → p3))) → False) → False) := by
  intro assump_1
  have assump_48 : (((True ∨ False) ∧ (False ∧ p5)) → ((p5 ∧ p2) ∧ (p6 → p3))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_9 =>
        apply False.elim assump_9
    cases assump_5
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        cases assump_19
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
      case inr assump_21 =>
        apply False.elim assump_21
    intro assump_30
    cases assump_5
    case intro assump_33 assump_34 =>
      cases assump_33
      case inl assump_35 =>
        cases assump_34
        case intro assump_39 assump_40 =>
          apply False.elim assump_39
      case inr assump_36 =>
        apply False.elim assump_36
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p4 p0 p2 p7 p6 p5 : Prop)
theorem file77_53124 : ((((((p4 ∧ False) → False) → ((p0 ∧ p0) → (p0 ∧ p6))) ∧ (((p2 ∧ False) → (p0 ∨ p5)) → False)) ∧ ((((p7 ∧ p4) → (p7 ∨ True)) ∨ ((False → p4) ∨ (True → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((p7 ∧ p4) → (p7 ∨ True)) ∨ ((False → p4) ∨ (True → False))) := by
        apply Or.inl
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inl
          exact assump_14
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p4 p7 p2 p6 p5 p3 p0 : Prop)
theorem file77_53820 : (((((p2 ∧ True) → (p6 ∧ p0)) → False) → (((p2 ∧ True) → False) → ((p0 → p6) → False))) → ((((p2 → p7) ∧ (False ∧ True)) → ((True ∨ p3) ∨ (p5 → False))) ∧ (((False → False) ∨ (True ∧ p0)) ∨ ((p5 → p4) ∧ (p4 → False))))) := by
  intro assump_15
  apply And.intro
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      apply False.elim assump_21
  apply Or.inl
  apply Or.inl
  intro assump_27
  apply False.elim assump_27


variable (p5 : Prop)
theorem file77_54366 : (((((p5 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p5 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p5 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p6 p1 p0 : Prop)
theorem file77_54788 : (((((p3 ∧ False) → False) ∧ ((False → p6) → False)) ∨ (((p3 → p3) → False) ∧ ((False ∨ p1) → (False ∧ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_31 : (False → p6) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_5 assump_31
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case intro assump_17 assump_18 =>
      have assump_32 : (p3 → p3) := by
        intro assump_25
        exact assump_25
      let assump_24 := assump_17 assump_32
      apply False.elim assump_24


variable (p2 p1 : Prop)
theorem file77_55491 : (((((False ∧ p1) → False) ∨ ((False → p2) ∨ (p2 ∨ False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p1) → False) ∨ ((False → p2) ∨ (p2 ∨ False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p7 p2 p3 p4 p6 p5 : Prop)
theorem file77_55924 : (((((True → False) ∧ (False → p1)) → ((p3 → False) ∨ (p2 → False))) → False) → ((((p7 → p1) ∨ (p3 → p4)) → ((p6 ∧ p3) ∨ (p2 ∧ p5))) → False)) := by
  intro assump_9
  intro assump_10
  have assump_35 : (((True → False) ∧ (False → p1)) → ((p3 → False) ∨ (p2 → False))) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply Or.inl
      intro assump_23
      have assump_36 : True := by
        apply True.intro
      let assump_28 := assump_17 assump_36
      apply False.elim assump_28
  let assump_15 := assump_9 assump_35
  apply False.elim assump_15


variable (p5 p3 p0 p2 p4 p1 : Prop)
theorem file77_56579 : (((((p4 ∨ p1) → (False → p1)) ∧ ((p2 ∧ p4) → False)) → (((p4 → p4) → (p3 → p1)) → ((p5 ∧ p0) ∧ (p0 → False)))) → ((((p1 → p4) ∧ (p5 ∧ True)) → ((False → False) ∨ (p5 → p1))) → (((True ∧ p2) → False) → ((p3 → p3) ∨ (p5 ∧ p4))))) := by
  intro assump_9
  intro assump_10
  intro assump_11
  apply Or.inl
  intro assump_18
  exact assump_18


variable (p4 p1 p5 p6 p2 p7 : Prop)
theorem file77_56977 : (((((False → False) → False) → ((p6 ∨ p1) ∧ (p5 ∧ False))) → False) → ((((p6 ∧ p2) → (p2 → False)) ∧ ((p6 ∨ p4) → False)) ∨ (((p7 ∧ p5) → (p1 → False)) → ((True → False) ∧ (True → False))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    have assump_108 : (((False → False) → False) → ((p6 ∨ p1) ∧ (p5 ∧ False))) := by
      intro assump_18
      apply And.intro
      apply Or.inl
      exact assump_8
      apply And.intro
      have assump_109 : (False → False) := by
        intro assump_24
        apply False.elim assump_24
      let assump_23 := assump_18 assump_109
      apply False.elim assump_23
      have assump_110 : (False → False) := by
        intro assump_33
        apply False.elim assump_33
      let assump_32 := assump_18 assump_110
      apply False.elim assump_32
    let assump_17 := assump_1 assump_108
    apply False.elim assump_17
  intro assump_42
  cases assump_42
  case inl assump_43 =>
    have assump_111 : (((False → False) → False) → ((p6 ∨ p1) ∧ (p5 ∧ False))) := by
      intro assump_49
      apply And.intro
      apply Or.inl
      exact assump_43
      apply And.intro
      have assump_112 : (False → False) := by
        intro assump_55
        apply False.elim assump_55
      let assump_54 := assump_49 assump_112
      apply False.elim assump_54
      have assump_113 : (False → False) := by
        intro assump_64
        apply False.elim assump_64
      let assump_63 := assump_49 assump_113
      apply False.elim assump_63
    let assump_48 := assump_1 assump_111
    apply False.elim assump_48
  case inr assump_44 =>
    have assump_114 : (((False → False) → False) → ((p6 ∨ p1) ∧ (p5 ∧ False))) := by
      intro assump_77
      apply And.intro
      have assump_115 : (False → False) := by
        intro assump_81
        apply False.elim assump_81
      let assump_80 := assump_77 assump_115
      apply False.elim assump_80
      apply And.intro
      have assump_116 : (False → False) := by
        intro assump_90
        apply False.elim assump_90
      let assump_89 := assump_77 assump_116
      apply False.elim assump_89
      have assump_117 : (False → False) := by
        intro assump_99
        apply False.elim assump_99
      let assump_98 := assump_77 assump_117
      apply False.elim assump_98
    let assump_76 := assump_1 assump_114
    apply False.elim assump_76


variable (p4 p5 p1 p2 p0 p3 : Prop)
theorem file77_59477 : (((((p5 ∨ False) → False) ∧ ((p2 ∨ p3) ∧ (p1 ∨ p0))) ∨ (((p4 ∧ False) ∧ (True → p2)) ∧ ((p3 → p0) → False))) → ((((False ∨ p5) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            have assump_125 : ((False ∨ p5) → False) := by
              intro assump_25
              cases assump_25
              case inl assump_26 =>
                apply False.elim assump_26
              case inr assump_27 =>
                have assump_126 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_27
                let assump_35 := assump_7 assump_126
                apply False.elim assump_35
            let assump_24 := assump_2 assump_125
            apply False.elim assump_24
          case inr assump_18 =>
            have assump_127 : ((False ∨ p5) → False) := by
              intro assump_48
              cases assump_48
              case inl assump_49 =>
                apply False.elim assump_49
              case inr assump_50 =>
                have assump_128 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_50
                let assump_58 := assump_7 assump_128
                apply False.elim assump_58
            let assump_47 := assump_2 assump_127
            apply False.elim assump_47
        case inr assump_14 =>
          cases assump_12
          case inl assump_67 =>
            have assump_129 : ((False ∨ p5) → False) := by
              intro assump_75
              cases assump_75
              case inl assump_76 =>
                apply False.elim assump_76
              case inr assump_77 =>
                have assump_130 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_77
                let assump_85 := assump_7 assump_130
                apply False.elim assump_85
            let assump_74 := assump_2 assump_129
            apply False.elim assump_74
          case inr assump_68 =>
            have assump_131 : ((False ∨ p5) → False) := by
              intro assump_98
              cases assump_98
              case inl assump_99 =>
                apply False.elim assump_99
              case inr assump_100 =>
                have assump_132 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_100
                let assump_108 := assump_7 assump_132
                apply False.elim assump_108
            let assump_97 := assump_2 assump_131
            apply False.elim assump_97
  case inr assump_6 =>
    cases assump_6
    case intro assump_115 assump_116 =>
      cases assump_115
      case intro assump_117 assump_118 =>
        cases assump_117
        case intro assump_119 assump_120 =>
          apply False.elim assump_120


variable (p6 p1 p2 p4 p5 : Prop)
theorem file77_62551 : ((((((p4 → p5) ∨ (p1 ∧ p6)) ∧ ((False → p2) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p4 → p5) ∨ (p1 ∧ p6)) ∧ ((False → p2) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_40 : (False → p2) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_40
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_21 assump_22 =>
          have assump_41 : (False → p2) := by
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_7 assump_41
          apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p1 p3 p2 p4 p0 p5 : Prop)
theorem file77_63462 : (((((False → False) ∨ (p0 ∧ p2)) → False) → False) ∨ ((((p1 ∧ p1) ∨ (p4 → p3)) → ((False ∧ p5) ∨ (True → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (p0 ∧ p2)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p1 p6 p2 p0 : Prop)
theorem file77_63864 : (((((p5 ∨ True) → False) → False) → False) → ((((p2 → False) ∨ (p0 → False)) → ((p1 → False) ∧ (True → False))) → (((p6 ∨ True) ∨ (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      have assump_59 : (((p5 ∨ True) → False) → False) := by
        intro assump_15
        have assump_60 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_18 := assump_15 assump_60
        apply False.elim assump_18
      let assump_14 := assump_1 assump_59
      apply False.elim assump_14
    case inr assump_7 =>
      have assump_61 : (((p5 ∨ True) → False) → False) := by
        intro assump_32
        have assump_62 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_35 := assump_32 assump_62
        apply False.elim assump_35
      let assump_31 := assump_1 assump_61
      apply False.elim assump_31
  case inr assump_5 =>
    have assump_63 : (((p5 ∨ True) → False) → False) := by
      intro assump_49
      have assump_64 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_52 := assump_49 assump_64
      apply False.elim assump_52
    let assump_48 := assump_1 assump_63
    apply False.elim assump_48


variable (p6 p3 p7 p1 p2 p5 p0 : Prop)
theorem file77_65254 : (((((p7 → False) ∧ (p6 ∧ p6)) → ((p6 → False) → (p5 → False))) → False) → ((((p0 → False) → (p1 ∨ p1)) ∨ ((p1 → p3) ∧ (p1 ∨ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_107 : (((p7 → False) ∧ (p6 ∧ p6)) → ((p6 → False) → (p5 → False))) := by
      intro assump_10
      intro assump_11
      intro assump_12
      cases assump_10
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          have assump_108 : p6 := by
            exact assump_22
          let assump_30 := assump_11 assump_108
          apply False.elim assump_30
    let assump_9 := assump_1 assump_107
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_37 assump_38 =>
      cases assump_38
      case inl assump_41 =>
        have assump_109 : (((p7 → False) ∧ (p6 ∧ p6)) → ((p6 → False) → (p5 → False))) := by
          intro assump_48
          intro assump_49
          intro assump_50
          cases assump_48
          case intro assump_55 assump_56 =>
            cases assump_56
            case intro assump_59 assump_60 =>
              have assump_110 : p6 := by
                exact assump_60
              let assump_68 := assump_49 assump_110
              apply False.elim assump_68
        let assump_47 := assump_1 assump_109
        apply False.elim assump_47
      case inr assump_42 =>
        have assump_111 : (((p7 → False) ∧ (p6 ∧ p6)) → ((p6 → False) → (p5 → False))) := by
          intro assump_80
          intro assump_81
          intro assump_82
          cases assump_80
          case intro assump_87 assump_88 =>
            cases assump_88
            case intro assump_91 assump_92 =>
              have assump_112 : p6 := by
                exact assump_92
              let assump_100 := assump_81 assump_112
              apply False.elim assump_100
        let assump_79 := assump_1 assump_111
        apply False.elim assump_79


variable (p7 p6 p5 p3 p2 : Prop)
theorem file77_67316 : ((((((p6 → p2) ∧ (False ∧ False)) → False) ∨ (((p7 ∨ p2) ∨ (p5 → False)) ∨ ((p7 → p7) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p6 → p2) ∧ (False ∧ False)) → False) ∨ (((p7 ∨ p2) ∨ (p5 → False)) ∨ ((p7 → p7) → (p3 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 p3 p2 p0 p1 p4 : Prop)
theorem file77_67903 : ((((((p5 ∧ p4) → False) ∧ ((p0 → False) ∨ (p6 ∨ p1))) → False) ∧ ((((p3 ∧ p2) ∧ (p2 ∧ p1)) → ((p4 ∧ False) → False)) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_31 : (((p3 ∧ p2) ∧ (p2 ∧ p1)) → ((p4 ∧ False) → False)) := by
      intro assump_20
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
    let assump_19 := assump_14 assump_31
    apply False.elim assump_19


variable (p3 p0 p6 p1 p5 p7 : Prop)
theorem file77_68468 : (((((p3 ∧ False) → False) → False) → (((p0 → False) ∨ (p5 ∧ False)) ∨ ((p5 ∨ p7) → (p0 ∧ p7)))) ∨ ((((p5 → p7) → (p0 → False)) → ((True ∨ True) ∨ (p6 → p0))) ∧ (((p3 ∧ p1) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_19 : ((p3 ∧ False) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p5 p7 p2 p1 p0 p6 : Prop)
theorem file77_69027 : ((((((False ∨ p2) → False) ∨ ((p7 → False) ∨ (p5 ∧ p0))) ∨ (((p1 ∨ p6) → False) → False)) ∧ ((((p7 ∧ p0) → (True → False)) → ((p6 → True) ∨ (p7 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_62 : (((p7 ∧ p0) → (True → False)) → ((p6 → True) ∨ (p7 ∧ p6))) := by
          intro assump_13
          apply Or.inl
          intro assump_16
          apply True.intro
        let assump_12 := assump_3 assump_62
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_20 =>
          have assump_63 : (((p7 ∧ p0) → (True → False)) → ((p6 → True) ∨ (p7 ∧ p6))) := by
            intro assump_27
            apply Or.inl
            intro assump_30
            apply True.intro
          let assump_26 := assump_3 assump_63
          apply False.elim assump_26
        case inr assump_21 =>
          cases assump_21
          case intro assump_34 assump_35 =>
            have assump_64 : (((p7 ∧ p0) → (True → False)) → ((p6 → True) ∨ (p7 ∧ p6))) := by
              intro assump_43
              apply Or.inl
              intro assump_46
              apply True.intro
            let assump_42 := assump_3 assump_64
            apply False.elim assump_42
    case inr assump_5 =>
      have assump_65 : (((p7 ∧ p0) → (True → False)) → ((p6 → True) ∨ (p7 ∧ p6))) := by
        intro assump_55
        apply Or.inl
        intro assump_58
        apply True.intro
      let assump_54 := assump_3 assump_65
      apply False.elim assump_54


variable (p1 p6 p5 p4 p7 p0 : Prop)
theorem file77_70741 : (((((False ∧ p6) → (p1 ∧ p7)) → False) → False) ∨ ((((p6 → False) ∨ (True ∨ p7)) → ((p7 ∧ p5) ∨ (p7 ∨ True))) ∨ (((p4 → False) ∨ (p1 → False)) ∨ ((p0 ∨ True) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_17 : ((False ∧ p6) → (p1 ∧ p7)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 p1 : Prop)
theorem file77_71340 : ((((((True → False) ∧ (False → False)) → ((p6 → p5) → False)) → False) ∨ ((((False → p1) → False) → ((p5 ∨ p5) ∧ (p1 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_43 : (((True → False) ∧ (False → False)) → ((p6 → p5) → False)) := by
      intro assump_7
      intro assump_8
      cases assump_7
      case intro assump_11 assump_12 =>
        have assump_44 : True := by
          apply True.intro
        let assump_18 := assump_11 assump_44
        apply False.elim assump_18
    let assump_6 := assump_2 assump_43
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_45 : (((False → p1) → False) → ((p5 ∨ p5) ∧ (p1 ∨ True))) := by
      intro assump_28
      apply And.intro
      have assump_46 : (False → p1) := by
        intro assump_32
        apply False.elim assump_32
      let assump_31 := assump_28 assump_46
      apply False.elim assump_31
      apply Or.inr
      apply True.intro
    let assump_27 := assump_3 assump_45
    apply False.elim assump_27


variable (p6 p2 p4 p0 p3 p5 : Prop)
theorem file77_72447 : ((((((p6 ∧ p0) → (p5 → p0)) ∧ ((p5 ∧ False) → (True → False))) ∧ (((p2 ∧ p3) → False) → ((p4 → p5) → (p6 → True)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 ∧ p0) → (p5 → p0)) ∧ ((p5 ∧ False) → (True → False))) ∧ (((p2 ∧ p3) → False) → ((p4 → p5) → (p6 → True)))) := by
    apply And.intro
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_10
    intro assump_15
    intro assump_16
    cases assump_15
    case intro assump_19 assump_20 =>
      apply False.elim assump_20
    intro assump_25
    intro assump_26
    intro assump_27
    apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p0 p7 p4 p1 p5 p2 p3 p6 : Prop)
theorem file77_73242 : (((((p0 ∨ True) ∨ (p5 → True)) → False) → (((p5 ∨ False) → False) → ((False ∨ p1) ∧ (False → False)))) ∨ ((((p0 → p0) ∧ (p0 ∨ True)) → ((p5 ∧ p7) → (p5 → p1))) → (((p0 ∨ p0) ∨ (p7 ∨ p6)) → ((p7 ∧ p2) ∨ (p3 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  have assump_14 : ((p0 ∨ True) ∨ (p5 → True)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7
  intro assump_11
  apply False.elim assump_11


variable (p1 p3 p7 p0 p2 : Prop)
theorem file77_73808 : (((((False ∨ True) ∧ (p3 ∨ True)) → False) → (((p3 → p3) ∧ (p0 ∨ p3)) ∧ ((p7 → p0) → (p2 → False)))) ∨ ((((p1 ∧ p3) ∨ (p0 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  exact assump_2
  have assump_25 : ((False ∨ True) ∧ (p3 ∨ True)) := by
    apply And.intro
    apply Or.inr
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_9 := assump_1 assump_25
  apply False.elim assump_9
  intro assump_13
  intro assump_14
  have assump_26 : ((False ∨ True) ∧ (p3 ∨ True)) := by
    apply And.intro
    apply Or.inr
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_21 := assump_1 assump_26
  apply False.elim assump_21


variable (p4 p5 p3 p7 p1 p6 : Prop)
theorem file77_74599 : (((((False ∨ p5) → False) ∧ ((True ∧ p7) ∨ (p5 ∧ p3))) → (((p3 ∨ False) ∧ (p6 ∨ p6)) ∨ ((p5 ∧ p6) ∨ (p1 → p7)))) ∨ ((((p5 → False) ∨ (False → p4)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        apply Or.inr
        intro assump_14
        exact assump_9
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        apply Or.inr
        apply Or.inr
        intro assump_23
        have assump_33 : (False ∨ p5) := by
          apply Or.inr
          exact assump_17
        let assump_29 := assump_2 assump_33
        apply False.elim assump_29


variable (p0 p7 p2 p1 p6 : Prop)
theorem file77_75427 : (((((p7 ∨ p7) → (True → False)) ∧ ((True → False) ∨ (p6 → p0))) ∧ (((p1 ∧ False) → False) ∧ ((p7 ∨ False) ∧ (p2 → False)))) → False) := by
  intro assump_85
  cases assump_85
  case intro assump_86 assump_87 =>
    cases assump_86
    case intro assump_88 assump_89 =>
      cases assump_89
      case inl assump_92 =>
        cases assump_87
        case intro assump_96 assump_97 =>
          cases assump_97
          case intro assump_100 assump_101 =>
            cases assump_100
            case inl assump_102 =>
              have assump_142 : True := by
                apply True.intro
              let assump_111 := assump_92 assump_142
              apply False.elim assump_111
            case inr assump_103 =>
              apply False.elim assump_103
      case inr assump_93 =>
        cases assump_87
        case intro assump_119 assump_120 =>
          cases assump_120
          case intro assump_123 assump_124 =>
            cases assump_123
            case inl assump_125 =>
              have assump_143 : (p7 ∨ p7) := by
                apply Or.inl
                exact assump_125
              let assump_135 := assump_88 assump_143
              have assump_144 : True := by
                apply True.intro
              let assump_136 := assump_135 assump_144
              apply False.elim assump_136
            case inr assump_126 =>
              apply False.elim assump_126


variable (p5 p7 p3 p1 p0 : Prop)
theorem file77_76898 : ((((((p1 → False) → (p7 → p3)) → False) → (((p0 ∨ p5) → False) → False)) ∧ ((((p0 → p5) ∧ (p7 ∨ p1)) ∨ ((p7 → False) ∨ (p1 → p5))) ∧ (((p5 ∧ False) ∨ (p0 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_54 : ((p5 ∧ False) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_21
              apply True.intro
            let assump_20 := assump_7 assump_54
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_55 : ((p5 ∧ False) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_30
              apply True.intro
            let assump_29 := assump_7 assump_55
            apply False.elim assump_29
      case inr assump_9 =>
        cases assump_9
        case inl assump_34 =>
          have assump_56 : ((p5 ∧ False) ∨ (p0 → True)) := by
            apply Or.inr
            intro assump_41
            apply True.intro
          let assump_40 := assump_7 assump_56
          apply False.elim assump_40
        case inr assump_35 =>
          have assump_57 : ((p5 ∧ False) ∨ (p0 → True)) := by
            apply Or.inr
            intro assump_50
            apply True.intro
          let assump_49 := assump_7 assump_57
          apply False.elim assump_49


variable (p1 p6 p0 p4 p7 p5 p2 p3 : Prop)
theorem file77_78521 : ((((((p4 → False) ∨ (p6 ∨ p0)) → ((p5 ∨ p3) → (p7 ∨ p2))) ∧ (((p3 → True) → False) ∧ ((True ∧ p3) → (p1 → False)))) ∧ ((((p5 ∧ False) ∧ (True → False)) ∧ ((False → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : (p3 → True) := by
          intro assump_19
          apply True.intro
        let assump_18 := assump_8 assump_23
        apply False.elim assump_18


variable (p0 p4 p5 p7 p6 p1 p2 : Prop)
theorem file77_79147 : (((((p1 → False) ∧ (p2 ∧ p1)) ∧ ((False → p4) ∨ (p6 ∧ p2))) → False) ∨ ((((False ∨ p1) ∨ (False ∨ p7)) → ((p5 ∧ p0) ∧ (True → False))) ∨ (((p1 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          have assump_39 : p1 := by
            exact assump_9
          let assump_21 := assump_4 assump_39
          apply False.elim assump_21
        case inr assump_15 =>
          cases assump_15
          case intro assump_25 assump_26 =>
            have assump_40 : p1 := by
              exact assump_9
            let assump_35 := assump_4 assump_40
            apply False.elim assump_35


variable (p4 p6 p7 p0 : Prop)
theorem file77_80029 : ((((((p0 ∨ p0) ∧ (p6 → p7)) ∧ ((p4 ∧ False) → (p6 → False))) → (((p4 ∧ False) ∧ (True → False)) → ((p7 → True) ∨ (p7 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∨ p0) ∧ (p6 → p7)) ∧ ((p4 ∧ False) → (p6 → False))) → (((p4 ∧ False) ∧ (True → False)) → ((p7 → True) ∨ (p7 ∨ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p5 p4 p3 p7 p2 p1 p6 : Prop)
theorem file77_80670 : (((((p0 → p3) ∧ (False → p1)) → False) → (((p2 ∨ p4) ∧ (p0 ∨ p3)) → ((p7 → p0) ∨ (False ∧ p3)))) ∨ ((((p0 → p3) ∨ (p6 ∧ p4)) → ((p6 → False) ∨ (True ∨ p5))) ∧ (((p1 → p7) → (p4 → False)) ∨ ((p1 → p3) → False)))) := by
  apply Or.inl
  intro assump_46
  intro assump_47
  cases assump_47
  case intro assump_48 assump_49 =>
    cases assump_48
    case inl assump_50 =>
      cases assump_49
      case inl assump_54 =>
        apply Or.inl
        intro assump_60
        exact assump_54
      case inr assump_55 =>
        apply Or.inl
        intro assump_67
        have assump_110 : ((p0 → p3) ∧ (False → p1)) := by
          apply And.intro
          intro assump_72
          exact assump_55
          intro assump_75
          apply False.elim assump_75
        let assump_71 := assump_46 assump_110
        apply False.elim assump_71
    case inr assump_51 =>
      cases assump_49
      case inl assump_83 =>
        apply Or.inl
        intro assump_89
        exact assump_83
      case inr assump_84 =>
        apply Or.inl
        intro assump_96
        have assump_111 : ((p0 → p3) ∧ (False → p1)) := by
          apply And.intro
          intro assump_101
          exact assump_84
          intro assump_104
          apply False.elim assump_104
        let assump_100 := assump_46 assump_111
        apply False.elim assump_100


variable (p5 p2 p3 p7 p6 p0 p1 p4 : Prop)
theorem file77_82082 : (((((p4 ∧ p7) → (p6 ∨ p7)) ∨ ((p6 → False) ∨ (p4 ∨ p3))) ∨ (((False ∨ p5) ∧ (p4 ∧ False)) → ((p6 ∧ p1) ∧ (p1 ∧ True)))) ∧ ((((p7 ∨ True) ∧ (False ∨ True)) ∧ ((p2 ∨ p0) ∧ (False ∨ p1))) ∨ (((p7 ∧ False) ∧ (p0 → p2)) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    exact assump_3
  apply Or.inr
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      apply False.elim assump_12


variable (p0 p3 p5 p1 : Prop)
theorem file77_82694 : (((((False ∨ p5) ∧ (p3 → False)) ∨ ((False → p1) ∨ (p5 ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False ∨ p5) ∧ (p3 → False)) ∨ ((False → p1) ∨ (p5 ∨ p0))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p7 p1 p2 p4 p5 p3 p0 : Prop)
theorem file77_83098 : (((((p7 ∨ p5) → False) ∨ ((p0 → p1) ∧ (p4 ∧ p3))) ∧ (((p2 ∧ p7) ∧ (True → False)) ∧ ((p2 → False) ∧ (p1 → p6)))) → ((((p3 → False) → False) ∨ ((p4 → p1) → (True → False))) → False)) := by
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
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              cases assump_14
              case intro assump_25 assump_26 =>
                have assump_133 : p2 := by
                  exact assump_17
                let assump_32 := assump_25 assump_133
                apply False.elim assump_32
      case inr assump_10 =>
        cases assump_10
        case intro assump_36 assump_37 =>
          cases assump_37
          case intro assump_40 assump_41 =>
            cases assump_8
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                cases assump_48
                case intro assump_50 assump_51 =>
                  cases assump_47
                  case intro assump_58 assump_59 =>
                    have assump_134 : p2 := by
                      exact assump_50
                    let assump_65 := assump_58 assump_134
                    apply False.elim assump_65
  case inr assump_4 =>
    cases assump_1
    case intro assump_71 assump_72 =>
      cases assump_71
      case inl assump_73 =>
        cases assump_72
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              cases assump_78
              case intro assump_89 assump_90 =>
                have assump_135 : p2 := by
                  exact assump_81
                let assump_96 := assump_89 assump_135
                apply False.elim assump_96
      case inr assump_74 =>
        cases assump_74
        case intro assump_100 assump_101 =>
          cases assump_101
          case intro assump_104 assump_105 =>
            cases assump_72
            case intro assump_110 assump_111 =>
              cases assump_110
              case intro assump_112 assump_113 =>
                cases assump_112
                case intro assump_114 assump_115 =>
                  cases assump_111
                  case intro assump_122 assump_123 =>
                    have assump_136 : p2 := by
                      exact assump_114
                    let assump_129 := assump_122 assump_136
                    apply False.elim assump_129


variable (p7 p2 p4 p5 : Prop)
theorem file77_85937 : (((((p2 ∧ p5) → False) → ((p7 → False) → False)) ∧ (((True ∧ p5) → (p4 → p5)) → False)) → ((((False → p7) → False) ∧ ((False ∨ p5) ∧ (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          have assump_37 : ((True ∧ p5) → (p4 → p5)) := by
            intro assump_24
            intro assump_25
            cases assump_24
            case intro assump_28 assump_29 =>
              exact assump_29
          let assump_23 := assump_18 assump_37
          apply False.elim assump_23


variable (p4 p5 p1 : Prop)
theorem file77_86773 : (((((p1 ∧ p4) → (False ∧ p1)) → ((True ∧ False) → (False ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p1 ∧ p4) → (False ∧ p1)) → ((True ∧ False) → (False ∧ p5))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
    cases assump_6
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p7 p6 p3 p4 p1 p5 : Prop)
theorem file77_87330 : (((((p6 ∨ p1) → (p1 ∨ p6)) ∨ ((False → False) → (p3 ∨ p2))) → False) → ((((p5 → p4) ∧ (False ∧ p4)) ∨ ((p3 → False) → False)) ∨ (((False → False) → False) ∧ ((False ∧ True) ∧ (p7 ∧ p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_19
  have assump_34 : (((p6 ∨ p1) → (p1 ∨ p6)) ∨ ((False → False) → (p3 ∨ p2))) := by
    apply Or.inl
    intro assump_24
    cases assump_24
    case inl assump_25 =>
      apply Or.inr
      exact assump_25
    case inr assump_26 =>
      apply Or.inl
      exact assump_26
  let assump_23 := assump_1 assump_34
  apply False.elim assump_23


variable (p2 p0 p3 p1 p5 p7 p4 : Prop)
theorem file77_87994 : (((((p3 → False) ∧ (False → False)) ∨ ((p7 → p1) ∧ (p0 ∨ p3))) ∧ (((p0 ∨ p2) ∧ (p5 → p3)) → False)) → ((((p0 → False) ∧ (True → False)) ∨ ((p0 ∧ p3) ∧ (p7 ∨ p3))) → (((False → False) ∨ (p7 ∧ p0)) ∨ ((p4 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply Or.inl
            apply Or.inl
            intro assump_23
            apply False.elim assump_23
        case inr assump_14 =>
          cases assump_14
          case intro assump_26 assump_27 =>
            cases assump_27
            case inl assump_30 =>
              apply Or.inl
              apply Or.inl
              intro assump_36
              apply False.elim assump_36
            case inr assump_31 =>
              apply Or.inl
              apply Or.inl
              intro assump_43
              apply False.elim assump_43
  case inr assump_4 =>
    cases assump_4
    case intro assump_46 assump_47 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        cases assump_47
        case inl assump_54 =>
          cases assump_1
          case intro assump_58 assump_59 =>
            cases assump_58
            case inl assump_60 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                apply Or.inl
                apply Or.inl
                intro assump_70
                apply False.elim assump_70
            case inr assump_61 =>
              cases assump_61
              case intro assump_73 assump_74 =>
                cases assump_74
                case inl assump_77 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_83
                  apply False.elim assump_83
                case inr assump_78 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_90
                  apply False.elim assump_90
        case inr assump_55 =>
          cases assump_1
          case intro assump_95 assump_96 =>
            cases assump_95
            case inl assump_97 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                apply Or.inl
                apply Or.inl
                intro assump_107
                apply False.elim assump_107
            case inr assump_98 =>
              cases assump_98
              case intro assump_110 assump_111 =>
                cases assump_111
                case inl assump_114 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_120
                  apply False.elim assump_120
                case inr assump_115 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_127
                  apply False.elim assump_127


variable (p5 p6 p1 p3 : Prop)
theorem file77_91078 : (((((p1 ∨ p5) → (False → True)) ∨ ((p5 → False) → (p3 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_10 : (((p1 ∨ p5) → (False → True)) ∨ ((p5 → False) → (p3 ∨ p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p1 p7 p5 p2 p3 p4 : Prop)
theorem file77_91467 : (((((p4 → p4) ∨ (p5 → False)) ∨ ((p1 → False) → False)) ∧ (((False → True) ∨ (p2 → False)) → False)) → ((((p4 ∧ False) ∧ (False ∧ p2)) → ((p1 → False) ∨ (False → False))) ∨ (((p3 → p2) ∨ (p3 ∨ p7)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
      case inr assump_7 =>
        apply Or.inl
        intro assump_25
        cases assump_25
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
    case inr assump_5 =>
      apply Or.inl
      intro assump_38
      cases assump_38
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          apply False.elim assump_42


variable (p4 p7 p5 p6 p2 : Prop)
theorem file77_92597 : (((((p2 ∧ p2) ∨ (False → p6)) ∨ ((p7 → p5) ∨ (False ∧ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p2 ∧ p2) ∨ (False → p6)) ∨ ((p7 → p5) ∨ (False ∧ p4))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p0 p3 p1 : Prop)
theorem file77_92983 : (((((p0 → p0) ∨ (p0 ∨ True)) ∨ ((p7 → False) ∨ (p3 → p1))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p0 → p0) ∨ (p0 ∨ True)) ∨ ((p7 → False) ∨ (p3 → p1))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p1 p0 p6 p4 : Prop)
theorem file77_93362 : (((((True → False) → (p7 ∨ p0)) → ((True → False) ∧ (p4 ∧ True))) → (((p4 → p6) ∨ (p5 → p0)) ∨ ((p6 ∧ p6) → False))) ∨ ((((p4 → False) ∨ (p5 → True)) → False) ∨ (((p0 ∧ p4) → False) ∨ ((p1 ∨ p0) ∨ (p1 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_21 : ((True → False) → (p7 ∨ p0)) := by
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_22
    apply False.elim assump_12
  let assump_8 := assump_1 assump_21
  let assump_16 := And.left assump_8
  have assump_23 : True := by
    apply True.intro
  let assump_17 := assump_16 assump_23
  apply False.elim assump_17


variable (p5 p7 p6 p0 p2 p3 : Prop)
theorem file77_94110 : (((((p7 ∧ p6) → (p6 → False)) → ((p2 → p5) → False)) → (((p0 → p5) ∧ (p3 → False)) → False)) → ((((p0 → p0) ∨ (p2 ∧ p3)) ∨ ((p6 ∨ True) → False)) ∨ (((p5 ∨ p0) → False) ∨ ((False ∨ p2) ∧ (p6 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p6 p4 p0 p1 p3 p5 p7 : Prop)
theorem file77_94476 : (((((False ∧ p3) → (p0 → False)) ∨ ((p4 ∨ p0) ∨ (p7 → False))) ∨ (((p6 ∧ p0) → False) → ((p5 ∧ p1) ∧ (True → False)))) ∧ ((((True ∨ p3) → (True → False)) ∨ ((False → False) → (p0 ∧ False))) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    have assump_30 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_14 := assump_10 assump_30
    have assump_31 : True := by
      apply True.intro
    let assump_15 := assump_14 assump_31
    apply False.elim assump_15
  case inr assump_11 =>
    have assump_32 : (False → False) := by
      intro assump_22
      apply False.elim assump_22
    let assump_21 := assump_11 assump_32
    let assump_25 := And.right assump_21
    apply False.elim assump_25


variable (p7 p0 p1 p6 p5 p4 : Prop)
theorem file77_95447 : ((((((p1 → False) → False) → ((p5 ∧ True) ∨ (p4 ∨ p6))) ∧ (((True ∨ p4) ∧ (False ∧ p5)) ∧ ((False → p1) ∧ (p6 → p4)))) ∨ ((((p6 → False) → (p6 ∨ p7)) → ((p0 → p0) ∨ (p5 → p1))) → (((p4 → False) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
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
  case inr assump_3 =>
    have assump_43 : (((p6 → False) → (p6 ∨ p7)) → ((p0 → p0) ∨ (p5 → p1))) := by
      intro assump_29
      apply Or.inl
      intro assump_32
      exact assump_32
    let assump_28 := assump_3 assump_43
    have assump_44 : ((p4 → False) → (False → False)) := by
      intro assump_36
      intro assump_37
      apply False.elim assump_37
    let assump_35 := assump_28 assump_44
    apply False.elim assump_35


variable (p2 p6 p1 : Prop)
theorem file77_96732 : ((((((False ∧ False) ∧ (p2 → p2)) → False) ∨ (((p2 ∧ p6) ∨ (p2 ∧ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ False) ∧ (p2 → p2)) → False) ∨ (((p2 ∧ p6) ∨ (p2 ∧ p1)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p4 p3 p5 p2 p0 : Prop)
theorem file77_97265 : ((((((p4 ∨ p5) ∨ (p6 ∨ p3)) ∨ ((p2 ∨ p5) ∨ (p6 → False))) ∨ (((p0 → False) ∨ (p2 ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p4 ∨ p5) ∨ (p6 ∨ p3)) ∨ ((p2 ∨ p5) ∨ (p6 → False))) ∨ (((p0 → False) ∨ (p2 ∧ p5)) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    have assump_17 : ((((p4 ∨ p5) ∨ (p6 ∨ p3)) ∨ ((p2 ∨ p5) ∨ (p6 → False))) ∨ (((p0 → False) ∨ (p2 ∧ p5)) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p3 p0 p6 p5 p4 p2 p1 : Prop)
theorem file77_98015 : (((((p1 ∧ False) → (p1 → False)) ∨ ((False ∧ p3) ∧ (p7 ∧ p3))) → (((p0 ∧ True) ∧ (p2 → p4)) ∨ ((p1 ∨ p6) ∨ (True ∨ p3)))) ∨ ((((p7 ∧ True) ∧ (p4 ∨ p6)) → False) ∨ (((p5 ∨ p3) → (p0 ∧ p1)) ∧ ((p3 ∧ p3) → (p7 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p4 p6 p7 p2 p1 p0 p5 : Prop)
theorem file77_98618 : (((((p7 ∧ p5) ∧ (p6 ∨ p6)) → False) → (((p1 → p6) → False) → ((p6 ∧ p0) → False))) ∨ ((((p1 ∧ p7) ∨ (p4 → p2)) → False) ∧ (((True → False) → False) → ((p5 ∨ p2) ∧ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_22 : (p1 → p6) := by
      intro assump_16
      exact assump_4
    let assump_15 := assump_2 assump_22
    apply False.elim assump_15


variable (p3 p6 p0 p2 p7 : Prop)
theorem file77_99129 : (((((p2 ∧ False) → (p6 ∨ False)) → False) → (((p0 ∨ p6) → (p6 ∧ p7)) ∧ ((p6 ∨ p3) → False))) ∨ ((((True → False) ∧ (p7 → False)) ∧ ((p2 ∧ False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    have assump_89 : ((p2 ∧ False) → (p6 ∨ False)) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    let assump_9 := assump_1 assump_89
    apply False.elim assump_9
  case inr assump_4 =>
    exact assump_4
  cases assump_2
  case inl assump_24 =>
    have assump_90 : ((p2 ∧ False) → (p6 ∨ False)) := by
      intro assump_31
      cases assump_31
      case intro assump_32 assump_33 =>
        apply False.elim assump_33
    let assump_30 := assump_1 assump_90
    apply False.elim assump_30
  case inr assump_25 =>
    have assump_91 : ((p2 ∧ False) → (p6 ∨ False)) := by
      intro assump_46
      cases assump_46
      case intro assump_47 assump_48 =>
        apply False.elim assump_48
    let assump_45 := assump_1 assump_91
    apply False.elim assump_45
  intro assump_56
  cases assump_56
  case inl assump_57 =>
    have assump_92 : ((p2 ∧ False) → (p6 ∨ False)) := by
      intro assump_64
      cases assump_64
      case intro assump_65 assump_66 =>
        apply False.elim assump_66
    let assump_63 := assump_1 assump_92
    apply False.elim assump_63
  case inr assump_58 =>
    have assump_93 : ((p2 ∧ False) → (p6 ∨ False)) := by
      intro assump_79
      cases assump_79
      case intro assump_80 assump_81 =>
        apply False.elim assump_81
    let assump_78 := assump_1 assump_93
    apply False.elim assump_78


variable (p3 p5 p4 p1 p7 : Prop)
theorem file77_100906 : ((((((p4 → p7) ∧ (p1 ∧ p3)) → False) → False) ∧ ((((p1 ∨ p5) ∨ (False ∧ p1)) ∨ ((p3 ∨ True) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p1 ∨ p5) ∨ (False ∧ p1)) ∨ ((p3 ∨ True) ∨ (False → False))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p5 p6 p2 p0 p4 p7 : Prop)
theorem file77_101410 : ((((((False → False) ∨ (p5 → p6)) → False) → (((p0 ∧ False) ∨ (p2 → False)) ∨ ((p4 ∧ p7) ∧ (p5 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → False) ∨ (p5 → p6)) → False) → (((p0 ∧ False) ∨ (p2 → False)) ∨ ((p4 ∧ p7) ∧ (p5 ∧ p4)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_23 : ((False → False) ∨ (p5 → p6)) := by
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p5 p2 p0 : Prop)
theorem file77_102075 : (((((p4 ∧ p2) → (True ∨ p2)) ∨ ((True ∨ p0) ∧ (p5 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p4 ∧ p2) → (True ∨ p2)) ∨ ((True ∨ p0) ∧ (p5 ∨ p4))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p4 p3 p7 p6 : Prop)
theorem file77_102510 : (((((True ∧ False) → (p4 → False)) ∨ ((False ∨ True) → (p1 → p6))) ∨ (((False → False) ∨ (p1 → p6)) → False)) ∨ ((((p3 ∧ False) → False) → ((p7 ∨ p1) ∧ (p3 → True))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_11
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    apply False.elim assump_16


variable (p4 p5 p6 p1 p0 p7 p3 : Prop)
theorem file77_102921 : (((((p5 ∧ p4) ∧ (p5 → False)) ∧ ((p6 ∧ p3) → False)) → (((p1 ∧ p4) → False) → False)) ∨ ((((True ∧ p5) ∨ (p5 ∧ p4)) → ((p5 → False) → (p0 ∧ p6))) ∧ (((p7 ∨ False) → False) → ((True ∨ False) ∧ (p4 ∧ p5))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        have assump_28 : p5 := by
          exact assump_13
        let assump_24 := assump_12 assump_28
        apply False.elim assump_24


variable (p5 p0 p1 p4 p3 p2 : Prop)
theorem file77_103553 : (((((p2 ∨ p5) ∧ (p0 ∧ p0)) ∨ ((False ∨ p0) ∨ (False → p5))) → False) → ((((True → p1) ∨ (True ∧ p3)) ∨ ((p5 ∧ False) → (p0 → p4))) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    cases assump_11
    case inl assump_13 =>
      have assump_52 : (((p2 ∨ p5) ∧ (p0 ∧ p0)) ∨ ((False ∨ p0) ∨ (False → p5))) := by
        apply Or.inr
        apply Or.inr
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_9 assump_52
      apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case intro assump_26 assump_27 =>
        have assump_53 : (((p2 ∨ p5) ∧ (p0 ∧ p0)) ∨ ((False ∨ p0) ∨ (False → p5))) := by
          apply Or.inr
          apply Or.inr
          intro assump_35
          apply False.elim assump_35
        let assump_34 := assump_9 assump_53
        apply False.elim assump_34
  case inr assump_12 =>
    have assump_54 : (((p2 ∨ p5) ∧ (p0 ∧ p0)) ∨ ((False ∨ p0) ∨ (False → p5))) := by
      apply Or.inr
      apply Or.inr
      intro assump_46
      apply False.elim assump_46
    let assump_45 := assump_9 assump_54
    apply False.elim assump_45


variable (p4 p1 p3 p7 p2 p5 p0 p6 : Prop)
theorem file77_104790 : (((((False → p6) → False) → False) ∨ (((p4 → False) → (False ∨ p5)) → ((p5 → True) → False))) ∨ ((((p1 ∧ p4) ∨ (True ∧ p1)) ∨ ((p1 ∨ p2) ∨ (p0 ∧ p5))) ∧ (((p1 ∨ p3) ∨ (p5 → False)) → ((p7 ∨ p5) ∧ (p4 → p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → p6) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p4 p0 p1 p7 : Prop)
theorem file77_105262 : (((((p7 → False) ∨ (True → False)) ∧ ((p7 ∧ p4) ∨ (p7 ∧ p0))) → False) ∨ ((((p4 → False) → False) ∨ ((p1 ∨ p4) → (p4 → p4))) ∨ (((p0 ∨ p4) ∨ (False ∧ p6)) → ((p0 → p6) → (p6 → True))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_62 : p7 := by
            exact assump_10
          let assump_18 := assump_4 assump_62
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          have assump_63 : p7 := by
            exact assump_22
          let assump_30 := assump_4 assump_63
          apply False.elim assump_30
    case inr assump_5 =>
      cases assump_3
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          have assump_64 : True := by
            apply True.intro
          let assump_46 := assump_5 assump_64
          apply False.elim assump_46
      case inr assump_37 =>
        cases assump_37
        case intro assump_50 assump_51 =>
          have assump_65 : True := by
            apply True.intro
          let assump_58 := assump_5 assump_65
          apply False.elim assump_58


variable (p7 p1 p0 p5 p2 p4 p6 p3 : Prop)
theorem file77_106680 : (((((p4 → False) ∨ (p3 → False)) ∧ ((p5 ∧ p7) ∧ (p0 ∧ p2))) ∧ (((p7 → False) → (p6 → p6)) ∧ ((True → p5) ∨ (p4 ∨ p5)))) → ((((False → False) → False) ∧ ((p6 ∨ p1) → (p2 → p4))) → (((p0 ∧ p4) → (p5 → p0)) ∨ ((True ∨ p4) ∧ (p6 → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_18
              case intro assump_25 assump_26 =>
                cases assump_10
                case intro assump_31 assump_32 =>
                  cases assump_32
                  case inl assump_35 =>
                    apply Or.inl
                    intro assump_39
                    intro assump_40
                    cases assump_39
                    case intro assump_43 assump_44 =>
                      exact assump_43
                  case inr assump_36 =>
                    cases assump_36
                    case inl assump_49 =>
                      apply Or.inl
                      intro assump_53
                      intro assump_54
                      cases assump_53
                      case intro assump_57 assump_58 =>
                        exact assump_57
                    case inr assump_50 =>
                      apply Or.inl
                      intro assump_65
                      intro assump_66
                      cases assump_65
                      case intro assump_69 assump_70 =>
                        exact assump_69
        case inr assump_14 =>
          cases assump_12
          case intro assump_77 assump_78 =>
            cases assump_77
            case intro assump_79 assump_80 =>
              cases assump_78
              case intro assump_85 assump_86 =>
                cases assump_10
                case intro assump_91 assump_92 =>
                  cases assump_92
                  case inl assump_95 =>
                    apply Or.inl
                    intro assump_99
                    intro assump_100
                    cases assump_99
                    case intro assump_103 assump_104 =>
                      exact assump_103
                  case inr assump_96 =>
                    cases assump_96
                    case inl assump_109 =>
                      apply Or.inl
                      intro assump_113
                      intro assump_114
                      cases assump_113
                      case intro assump_117 assump_118 =>
                        exact assump_117
                    case inr assump_110 =>
                      apply Or.inl
                      intro assump_125
                      intro assump_126
                      cases assump_125
                      case intro assump_129 assump_130 =>
                        exact assump_129


variable (p6 p1 p3 p5 p0 p7 p4 p2 : Prop)
theorem file77_109815 : (((((False ∧ p6) → (p0 → p7)) → False) → (((p1 ∧ p5) ∧ (p7 → False)) → False)) ∨ ((((True ∨ p2) ∧ (p3 → p5)) ∨ ((p0 → True) → (p4 ∨ p7))) ∧ (((True ∧ p6) → (p5 → p5)) ∧ ((False ∨ p2) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_27 : ((False ∧ p6) → (p0 → p7)) := by
        intro assump_16
        intro assump_17
        cases assump_16
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
      let assump_15 := assump_1 assump_27
      apply False.elim assump_15


