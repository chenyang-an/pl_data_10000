variable (p6 p3 p7 p1 p5 : Prop)
theorem file53_41 : ((((((p5 → p7) → False) → False) → (((p3 → False) ∧ (False ∧ p5)) → ((True ∧ p6) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p5 → p7) → False) → False) → (((p3 → False) ∧ (False ∧ p5)) → ((True ∧ p6) → (p1 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p2 : Prop)
theorem file53_713 : ((((((p2 ∧ p6) → False) ∧ ((False → True) ∧ (p6 ∧ p2))) → (((p2 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p2 ∧ p6) → False) ∧ ((False → True) ∧ (p6 ∧ p2))) → (((p2 → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          have assump_34 : (p2 ∧ p6) := by
            apply And.intro
            exact assump_18
            exact assump_17
          let assump_26 := assump_9 assump_34
          apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p4 p7 p5 : Prop)
theorem file53_1512 : (((((False → p6) ∧ (p4 ∧ p6)) ∧ ((p6 ∧ p5) ∧ (p7 → False))) ∧ (((p6 ∧ p4) ∨ (p6 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_5
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_32 : ((p6 ∧ p4) ∨ (p6 → p6)) := by
                apply Or.inl
                apply And.intro
                exact assump_18
                exact assump_10
              let assump_28 := assump_3 assump_32
              apply False.elim assump_28


variable (p6 p2 p7 p0 p1 : Prop)
theorem file53_2348 : ((((((p6 ∨ True) → False) → False) ∨ (((p1 → False) ∧ (p0 ∨ p0)) ∧ ((p2 → False) ∧ (p7 ∨ p0)))) → False) → False) := by
  intro assump_13
  have assump_27 : ((((p6 ∨ True) → False) → False) ∨ (((p1 → False) ∧ (p0 ∨ p0)) ∧ ((p2 → False) ∧ (p7 ∨ p0)))) := by
    apply Or.inl
    intro assump_17
    have assump_28 : (p6 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_20 := assump_17 assump_28
    apply False.elim assump_20
  let assump_16 := assump_13 assump_27
  apply False.elim assump_16


variable (p7 p6 p0 p2 p5 : Prop)
theorem file53_2920 : ((((((False → False) ∨ (p5 ∧ p2)) ∨ ((p2 → p2) ∨ (p0 ∨ p6))) ∨ (((p7 ∨ p5) → False) → False)) → False) → False) := by
  intro assump_7
  have assump_17 : ((((False → False) ∨ (p5 ∧ p2)) ∨ ((p2 → p2) ∨ (p0 ∨ p6))) ∨ (((p7 ∨ p5) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_7 assump_17
  apply False.elim assump_10


variable (p4 p0 p7 p1 p2 p3 p5 p6 : Prop)
theorem file53_3407 : (((((p3 ∨ p6) → False) → ((p7 ∨ p3) → (p2 → p4))) → False) → ((((p5 ∧ p0) ∨ (p4 → p6)) ∨ ((p7 ∧ True) ∨ (p2 ∨ p1))) → (((p5 → p3) ∨ (p5 → False)) → ((p5 ∨ p6) → (p7 → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case inl assump_12 =>
      cases assump_2
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            exact assump_5
        case inr assump_19 =>
          exact assump_5
      case inr assump_17 =>
        cases assump_17
        case inl assump_32 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            exact assump_34
        case inr assump_33 =>
          cases assump_33
          case inl assump_42 =>
            exact assump_5
          case inr assump_43 =>
            exact assump_5
    case inr assump_13 =>
      cases assump_2
      case inl assump_54 =>
        cases assump_54
        case inl assump_56 =>
          cases assump_56
          case intro assump_58 assump_59 =>
            exact assump_5
        case inr assump_57 =>
          exact assump_5
      case inr assump_55 =>
        cases assump_55
        case inl assump_70 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            exact assump_72
        case inr assump_71 =>
          cases assump_71
          case inl assump_80 =>
            exact assump_5
          case inr assump_81 =>
            exact assump_5
  case inr assump_9 =>
    cases assump_3
    case inl assump_92 =>
      cases assump_2
      case inl assump_96 =>
        cases assump_96
        case inl assump_98 =>
          cases assump_98
          case intro assump_100 assump_101 =>
            exact assump_5
        case inr assump_99 =>
          exact assump_5
      case inr assump_97 =>
        cases assump_97
        case inl assump_112 =>
          cases assump_112
          case intro assump_114 assump_115 =>
            exact assump_114
        case inr assump_113 =>
          cases assump_113
          case inl assump_122 =>
            exact assump_5
          case inr assump_123 =>
            exact assump_5
    case inr assump_93 =>
      cases assump_2
      case inl assump_134 =>
        cases assump_134
        case inl assump_136 =>
          cases assump_136
          case intro assump_138 assump_139 =>
            exact assump_5
        case inr assump_137 =>
          exact assump_5
      case inr assump_135 =>
        cases assump_135
        case inl assump_150 =>
          cases assump_150
          case intro assump_152 assump_153 =>
            exact assump_152
        case inr assump_151 =>
          cases assump_151
          case inl assump_160 =>
            exact assump_5
          case inr assump_161 =>
            exact assump_5


variable (p4 p3 p0 p7 p5 p6 p2 : Prop)
theorem file53_6406 : (((((True ∨ False) → False) → False) ∧ (((p0 → True) ∨ (False → True)) ∨ ((p2 ∧ p5) → False))) ∨ ((((p7 ∧ True) → (p2 → p6)) ∨ ((p3 ∧ p7) ∧ (p4 → False))) ∨ (((p6 → False) ∨ (True ∧ p3)) → False))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_9 : (True ∨ False) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4
  apply Or.inl
  apply Or.inl
  intro assump_8
  apply True.intro


variable (p6 p4 p1 p2 p5 p3 p0 p7 : Prop)
theorem file53_6933 : (((((p3 → p1) ∧ (p4 ∧ p5)) ∧ ((False → False) ∨ (p0 ∧ True))) ∧ (((p5 ∨ False) ∧ (p4 → p7)) → ((False ∨ False) → False))) → ((((p2 ∨ p4) ∧ (p1 ∨ p4)) ∧ ((p2 → p7) → False)) → (((p0 → False) ∧ (p7 ∧ p1)) → ((p0 ∧ p6) → (p6 → False))))) := by
  intro assump_14
  intro assump_15
  intro assump_16
  intro assump_17
  intro assump_18
  cases assump_17
  case intro assump_21 assump_22 =>
    cases assump_16
    case intro assump_27 assump_28 =>
      cases assump_28
      case intro assump_31 assump_32 =>
        cases assump_15
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_39
            case inl assump_41 =>
              cases assump_40
              case inl assump_45 =>
                cases assump_14
                case intro assump_51 assump_52 =>
                  cases assump_51
                  case intro assump_53 assump_54 =>
                    cases assump_53
                    case intro assump_55 assump_56 =>
                      cases assump_56
                      case intro assump_59 assump_60 =>
                        cases assump_54
                        case inl assump_65 =>
                          have assump_307 : (p2 → p7) := by
                            intro assump_81
                            exact assump_31
                          let assump_80 := assump_38 assump_307
                          apply False.elim assump_80
                        case inr assump_66 =>
                          cases assump_66
                          case intro assump_87 assump_88 =>
                            have assump_308 : (p2 → p7) := by
                              intro assump_105
                              exact assump_31
                            let assump_104 := assump_38 assump_308
                            apply False.elim assump_104
              case inr assump_46 =>
                cases assump_14
                case intro assump_115 assump_116 =>
                  cases assump_115
                  case intro assump_117 assump_118 =>
                    cases assump_117
                    case intro assump_119 assump_120 =>
                      cases assump_120
                      case intro assump_123 assump_124 =>
                        cases assump_118
                        case inl assump_129 =>
                          have assump_309 : (p2 → p7) := by
                            intro assump_145
                            exact assump_31
                          let assump_144 := assump_38 assump_309
                          apply False.elim assump_144
                        case inr assump_130 =>
                          cases assump_130
                          case intro assump_151 assump_152 =>
                            have assump_310 : (p2 → p7) := by
                              intro assump_169
                              exact assump_31
                            let assump_168 := assump_38 assump_310
                            apply False.elim assump_168
            case inr assump_42 =>
              cases assump_40
              case inl assump_177 =>
                cases assump_14
                case intro assump_183 assump_184 =>
                  cases assump_183
                  case intro assump_185 assump_186 =>
                    cases assump_185
                    case intro assump_187 assump_188 =>
                      cases assump_188
                      case intro assump_191 assump_192 =>
                        cases assump_186
                        case inl assump_197 =>
                          have assump_311 : (p2 → p7) := by
                            intro assump_213
                            exact assump_31
                          let assump_212 := assump_38 assump_311
                          apply False.elim assump_212
                        case inr assump_198 =>
                          cases assump_198
                          case intro assump_219 assump_220 =>
                            have assump_312 : (p2 → p7) := by
                              intro assump_237
                              exact assump_31
                            let assump_236 := assump_38 assump_312
                            apply False.elim assump_236
              case inr assump_178 =>
                cases assump_14
                case intro assump_247 assump_248 =>
                  cases assump_247
                  case intro assump_249 assump_250 =>
                    cases assump_249
                    case intro assump_251 assump_252 =>
                      cases assump_252
                      case intro assump_255 assump_256 =>
                        cases assump_250
                        case inl assump_261 =>
                          have assump_313 : (p2 → p7) := by
                            intro assump_277
                            exact assump_31
                          let assump_276 := assump_38 assump_313
                          apply False.elim assump_276
                        case inr assump_262 =>
                          cases assump_262
                          case intro assump_283 assump_284 =>
                            have assump_314 : (p2 → p7) := by
                              intro assump_301
                              exact assump_31
                            let assump_300 := assump_38 assump_314
                            apply False.elim assump_300


variable (p3 p7 p2 p0 p5 : Prop)
theorem file53_12509 : ((((((p5 ∧ p2) ∧ (p0 ∨ p2)) → ((p7 → p2) ∨ (False → p3))) ∨ (((p5 ∨ False) ∧ (p3 ∧ False)) → ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 ∧ p2) ∧ (p0 ∨ p2)) → ((p7 → p2) ∨ (False → p3))) ∨ (((p5 ∨ False) ∧ (p3 ∧ False)) → ((p3 → False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          exact assump_9
        case inr assump_15 =>
          apply Or.inl
          intro assump_23
          exact assump_15
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p7 p3 p4 p2 : Prop)
theorem file53_13313 : ((((((p7 ∨ p7) ∨ (True → p2)) ∧ ((p7 ∨ True) ∨ (True ∧ p1))) → (((p3 ∧ p2) → (False → p4)) ∨ ((p1 → False) ∨ (p1 → False)))) → False) → False) := by
  intro assump_5
  have assump_103 : ((((p7 ∨ p7) ∨ (True → p2)) ∧ ((p7 ∨ True) ∨ (True ∧ p1))) → (((p3 ∧ p2) → (False → p4)) ∨ ((p1 → False) ∨ (p1 → False)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_11
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              intro assump_24
              intro assump_25
              apply False.elim assump_25
            case inr assump_21 =>
              apply Or.inl
              intro assump_30
              intro assump_31
              apply False.elim assump_31
          case inr assump_19 =>
            cases assump_19
            case intro assump_34 assump_35 =>
              apply Or.inl
              intro assump_40
              intro assump_41
              apply False.elim assump_41
        case inr assump_15 =>
          cases assump_11
          case inl assump_46 =>
            cases assump_46
            case inl assump_48 =>
              apply Or.inl
              intro assump_52
              intro assump_53
              apply False.elim assump_53
            case inr assump_49 =>
              apply Or.inl
              intro assump_58
              intro assump_59
              apply False.elim assump_59
          case inr assump_47 =>
            cases assump_47
            case intro assump_62 assump_63 =>
              apply Or.inl
              intro assump_68
              intro assump_69
              apply False.elim assump_69
      case inr assump_13 =>
        cases assump_11
        case inl assump_74 =>
          cases assump_74
          case inl assump_76 =>
            apply Or.inl
            intro assump_80
            intro assump_81
            apply False.elim assump_81
          case inr assump_77 =>
            apply Or.inl
            intro assump_86
            intro assump_87
            apply False.elim assump_87
        case inr assump_75 =>
          cases assump_75
          case intro assump_90 assump_91 =>
            apply Or.inl
            intro assump_96
            intro assump_97
            apply False.elim assump_97
  let assump_8 := assump_5 assump_103
  apply False.elim assump_8


variable (p6 p3 p0 p1 p5 p4 : Prop)
theorem file53_15884 : (((((p1 → False) → False) → ((False ∧ p1) → (p0 → False))) ∨ (((p0 → False) ∧ (p4 → False)) → ((p5 → p1) ∧ (p6 → False)))) ∨ ((((True ∨ True) ∨ (p0 → p6)) → False) ∨ (((p1 → p3) → (False ∨ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p2 p7 p5 p1 p4 p6 p3 : Prop)
theorem file53_16320 : (((((p7 ∧ p2) ∨ (False → True)) → ((p4 ∨ True) → False)) ∨ (((False ∧ p3) → (False ∧ p1)) → False)) → ((((p2 → False) ∧ (False ∨ p6)) → ((p6 ∧ p1) → (p5 → False))) ∧ (((False ∧ p6) → False) ∧ ((p7 → False) → (False → True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        apply False.elim assump_17
      case inr assump_18 =>
        cases assump_1
        case inl assump_23 =>
          have assump_55 : ((p7 ∧ p2) ∨ (False → True)) := by
            apply Or.inr
            intro assump_28
            apply True.intro
          let assump_27 := assump_23 assump_55
          have assump_56 : (p4 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_29 := assump_27 assump_56
          apply False.elim assump_29
        case inr assump_24 =>
          have assump_57 : ((False ∧ p3) → (False ∧ p1)) := by
            intro assump_36
            apply And.intro
            cases assump_36
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
            cases assump_36
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
          let assump_35 := assump_24 assump_57
          apply False.elim assump_35
  apply And.intro
  intro assump_48
  cases assump_48
  case intro assump_49 assump_50 =>
    apply False.elim assump_49
  intro assump_53
  intro assump_54
  apply True.intro


variable (p2 p7 p0 p1 p3 p4 : Prop)
theorem file53_17986 : (((((p0 ∨ p2) ∧ (False ∨ False)) → False) ∧ (((p1 → False) → (p4 ∧ p2)) ∧ ((p3 ∧ p3) ∧ (True → False)))) → ((((p1 → False) → False) → False) → (((p7 ∨ p2) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          have assump_30 : True := by
            apply True.intro
          let assump_26 := assump_17 assump_30
          apply False.elim assump_26


variable (p1 p3 p2 p7 p0 p5 p4 : Prop)
theorem file53_18668 : ((((((True → p7) ∨ (p0 ∨ p7)) → ((False → False) → False)) ∧ (((True ∧ p0) → False) → ((True → p5) ∨ (True → p5)))) ∧ ((((p4 ∧ p2) ∧ (p4 ∧ p3)) → ((p2 ∨ True) ∨ (p1 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_31 : (((p4 ∧ p2) ∧ (p4 ∧ p3)) → ((p2 ∨ True) ∨ (p1 → p3))) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              apply Or.inl
              apply Or.inl
              exact assump_17
      let assump_12 := assump_3 assump_31
      apply False.elim assump_12


variable (p5 p6 p4 p1 p3 p2 : Prop)
theorem file53_19525 : (((((p6 ∧ False) → False) → False) → False) ∨ ((((False → p1) ∧ (p1 ∧ p1)) → False) → (((p3 ∨ p5) ∨ (p4 → p2)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p6 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p3 p1 p4 p5 p7 p6 p2 : Prop)
theorem file53_19970 : ((((((p6 ∨ p1) → False) ∧ ((p0 ∨ p4) → (p2 ∨ p3))) ∧ (((p4 ∨ p3) ∧ (p1 ∧ p5)) → False)) ∧ ((((p3 → p5) → (p7 ∧ p3)) ∨ ((p3 ∨ p4) → (p1 → False))) ∧ (((p6 ∧ False) → (p1 → False)) → False))) → False) := by
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
            have assump_54 : ((p6 ∧ False) → (p1 → False)) := by
              intro assump_23
              intro assump_24
              cases assump_23
              case intro assump_27 assump_28 =>
                apply False.elim assump_28
            let assump_22 := assump_15 assump_54
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_55 : ((p6 ∧ False) → (p1 → False)) := by
              intro assump_41
              intro assump_42
              cases assump_41
              case intro assump_45 assump_46 =>
                apply False.elim assump_46
            let assump_40 := assump_15 assump_55
            apply False.elim assump_40


variable (p3 p7 p0 p2 p1 p4 : Prop)
theorem file53_21240 : ((((((p2 ∧ p7) → (p4 → False)) → False) ∨ (((p1 → False) → False) → False)) ∧ ((((p2 → True) ∨ (p0 → p7)) → ((p2 → False) ∨ (p4 ∧ p3))) ∧ (((p4 ∧ p4) → False) ∧ ((p4 → False) ∧ (p3 ∧ False))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
    case inr assump_9 =>
      cases assump_7
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          cases assump_37
          case intro assump_40 assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              apply False.elim assump_45


variable (p2 p1 p4 p0 p7 p6 p5 p3 : Prop)
theorem file53_22276 : ((((((p3 ∧ p2) ∨ (p1 → False)) ∨ ((p1 → False) → (p5 ∧ p2))) → (((p7 ∧ False) ∨ (p4 ∧ False)) → ((p6 → p0) ∧ (p6 → p2)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p3 ∧ p2) ∨ (p1 → False)) ∨ ((p1 → False) → (p5 ∧ p2))) → (((p7 ∧ False) ∨ (p4 ∧ False)) → ((p6 → p0) ∧ (p6 → p2)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    case inr assump_11 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        apply False.elim assump_19
    intro assump_24
    cases assump_6
    case inl assump_27 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        apply False.elim assump_30
    case inr assump_28 =>
      cases assump_28
      case intro assump_35 assump_36 =>
        apply False.elim assump_36
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p0 p6 p5 p2 p3 p1 p4 : Prop)
theorem file53_23339 : (((((p3 ∧ p1) → (p3 → False)) ∨ ((p3 ∨ p2) ∧ (p6 → p0))) ∨ (((True ∨ p3) → False) → ((p4 ∨ True) → False))) → ((((True → False) → (p4 ∧ p0)) ∨ ((p1 ∨ p5) → (p0 ∨ p2))) ∨ (((p1 → False) ∧ (p2 → False)) ∧ ((p2 ∧ True) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      intro assump_8
      apply And.intro
      have assump_74 : True := by
        apply True.intro
      let assump_11 := assump_8 assump_74
      apply False.elim assump_11
      have assump_75 : True := by
        apply True.intro
      let assump_17 := assump_8 assump_75
      apply False.elim assump_17
    case inr assump_5 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          apply Or.inl
          apply Or.inl
          intro assump_29
          apply And.intro
          have assump_76 : True := by
            apply True.intro
          let assump_32 := assump_29 assump_76
          apply False.elim assump_32
          have assump_77 : True := by
            apply True.intro
          let assump_38 := assump_29 assump_77
          apply False.elim assump_38
        case inr assump_24 =>
          apply Or.inl
          apply Or.inl
          intro assump_46
          apply And.intro
          have assump_78 : True := by
            apply True.intro
          let assump_49 := assump_46 assump_78
          apply False.elim assump_49
          have assump_79 : True := by
            apply True.intro
          let assump_55 := assump_46 assump_79
          apply False.elim assump_55
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_61
    apply And.intro
    have assump_80 : True := by
      apply True.intro
    let assump_64 := assump_61 assump_80
    apply False.elim assump_64
    have assump_81 : True := by
      apply True.intro
    let assump_70 := assump_61 assump_81
    apply False.elim assump_70


variable (p0 p1 p4 p3 p5 p7 : Prop)
theorem file53_25404 : ((((((p4 → False) → False) ∧ ((p0 ∨ p7) ∨ (p3 → p1))) → (((p5 → False) ∧ (p4 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p4 → False) → False) ∧ ((p0 ∨ p7) ∨ (p3 → p1))) → (((p5 → False) ∧ (p4 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p3 p7 p5 p2 : Prop)
theorem file53_25973 : (((((p2 ∧ p7) ∨ (p3 ∨ p5)) → False) ∧ (((p3 ∧ False) → (p0 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p3 ∧ False) → (p0 ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p7 p2 p6 p5 p3 p1 p0 : Prop)
theorem file53_26439 : ((((((p2 ∨ p6) → (p7 ∨ p7)) ∨ ((False ∧ p2) ∧ (p6 ∨ p5))) ∧ (((True → False) ∧ (p3 ∨ p7)) ∧ ((p1 ∧ p2) → (p1 → True)))) ∨ ((((p6 ∧ False) ∧ (False ∨ True)) ∨ ((p1 → False) → (p7 → True))) → (((False → p6) ∧ (False ∧ p5)) ∧ ((p0 → False) ∨ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_13
            case inl assump_16 =>
              have assump_56 : True := by
                apply True.intro
              let assump_24 := assump_12 assump_56
              apply False.elim assump_24
            case inr assump_17 =>
              have assump_57 : True := by
                apply True.intro
              let assump_34 := assump_12 assump_57
              apply False.elim assump_34
      case inr assump_7 =>
        cases assump_7
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_40
  case inr assump_3 =>
    have assump_58 : (((p6 ∧ False) ∧ (False ∨ True)) ∨ ((p1 → False) → (p7 → True))) := by
      apply Or.inr
      intro assump_47
      intro assump_48
      apply True.intro
    let assump_46 := assump_3 assump_58
    let assump_49 := And.left assump_46
    let assump_50 := And.right assump_49
    let assump_52 := And.left assump_50
    apply False.elim assump_52


variable (p3 p4 p6 p0 p1 : Prop)
theorem file53_28086 : (((((True ∧ p3) ∨ (p4 ∨ True)) ∨ ((p1 ∨ p4) ∨ (p1 → p6))) → False) → ((((p4 ∧ p3) ∨ (p0 → False)) ∧ ((p4 → False) → False)) ∧ (((p1 ∧ p1) ∧ (False ∨ p6)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inr
  intro assump_4
  have assump_42 : (((True ∧ p3) ∨ (p4 ∨ True)) ∨ ((p1 ∨ p4) ∨ (p1 → p6))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_8 := assump_1 assump_42
  apply False.elim assump_8
  intro assump_12
  have assump_43 : (((True ∧ p3) ∨ (p4 ∨ True)) ∨ ((p1 ∨ p4) ∨ (p1 → p6))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_17 := assump_1 assump_43
  apply False.elim assump_17
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      cases assump_23
      case inl assump_30 =>
        apply False.elim assump_30
      case inr assump_31 =>
        have assump_44 : (((True ∧ p3) ∨ (p4 ∨ True)) ∨ ((p1 ∨ p4) ∨ (p1 → p6))) := by
          apply Or.inl
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_38 := assump_1 assump_44
        apply False.elim assump_38


variable (p4 p2 p3 p0 p7 p1 p6 p5 : Prop)
theorem file53_29369 : (((((p4 → False) → False) → False) ∨ (((p5 → p2) ∧ (p7 → p3)) → False)) → ((((p6 → False) → (p3 ∨ True)) ∨ ((p0 → False) → False)) ∨ (((p5 ∧ p4) ∨ (p1 → False)) ∧ ((p2 ∨ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply Or.inr
    apply True.intro


variable (p6 p2 p0 p3 p7 p4 p1 : Prop)
theorem file53_29887 : ((((((False → p4) ∨ (True ∨ p6)) ∨ ((True ∨ p3) ∧ (p1 ∧ p1))) ∨ (((False → p2) ∨ (False → False)) → ((p0 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → p4) ∨ (True ∨ p6)) ∨ ((True ∨ p3) ∧ (p1 ∧ p1))) ∨ (((False → p2) ∨ (False → False)) → ((p0 ∨ p7) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p4 p1 p0 p3 p5 p7 p2 : Prop)
theorem file53_30426 : (((((p6 ∧ p1) ∨ (True ∨ p5)) → False) → False) ∨ ((((p5 ∧ p4) ∧ (p3 → False)) → ((p7 → p0) → (p5 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p6 ∧ p1) ∨ (True ∨ p5)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p0 p5 p1 p6 p3 p7 p4 : Prop)
theorem file53_30814 : (((((p4 ∧ p2) ∧ (True → False)) ∧ ((True ∧ p6) ∧ (p1 → p1))) ∧ (((p6 ∧ True) ∧ (p5 → p7)) ∧ ((p1 → p1) ∨ (False ∧ p2)))) → ((((False ∨ p0) → (p3 ∧ p0)) ∧ ((p6 ∨ True) ∧ (p3 ∧ p5))) ∨ (((p2 ∨ p1) ∨ (p7 → True)) ∨ ((p4 → False) ∨ (p4 ∧ p0))))) := by
  intro assump_40
  cases assump_40
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      cases assump_43
      case intro assump_45 assump_46 =>
        cases assump_45
        case intro assump_47 assump_48 =>
          cases assump_44
          case intro assump_55 assump_56 =>
            cases assump_55
            case intro assump_57 assump_58 =>
              cases assump_42
              case intro assump_65 assump_66 =>
                cases assump_65
                case intro assump_67 assump_68 =>
                  cases assump_67
                  case intro assump_69 assump_70 =>
                    cases assump_66
                    case inl assump_77 =>
                      apply Or.inr
                      apply Or.inl
                      apply Or.inl
                      apply Or.inl
                      exact assump_48
                    case inr assump_78 =>
                      cases assump_78
                      case intro assump_104 assump_105 =>
                        apply False.elim assump_104


variable (p0 p3 p7 p6 p4 : Prop)
theorem file53_32213 : (((((p7 → False) ∧ (p3 → False)) → False) ∧ (((p3 → p6) → False) ∧ ((p0 ∨ p7) ∧ (p4 ∧ False)))) → False) := by
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
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
        case inr assump_13 =>
          cases assump_11
          case intro assump_24 assump_25 =>
            apply False.elim assump_25


variable (p5 p0 p4 p1 p3 p6 p7 p2 : Prop)
theorem file53_32876 : (((((True ∨ p3) ∨ (p0 → False)) → ((p7 → False) ∧ (p6 → False))) ∨ (((p1 → True) ∨ (False → p3)) ∨ ((p0 ∨ p4) → False))) → ((((p5 → p7) → False) ∧ ((True ∨ p1) ∧ (p6 ∧ False))) → (((p2 ∧ p0) → False) → ((False → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_14
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
      case inr assump_16 =>
        cases assump_14
        case intro assump_27 assump_28 =>
          apply False.elim assump_28


variable (p5 p0 p7 p1 : Prop)
theorem file53_33629 : (((((p5 ∨ p7) ∨ (True ∨ p7)) → False) → (((p0 → False) → False) ∨ ((False → False) ∨ (p7 → p1)))) ∧ ((((p1 → False) ∧ (False ∨ p5)) ∧ ((p1 → p0) ∧ (True → False))) → (((p7 → False) → False) → False))) := by
  apply And.intro
  intro assump_7
  apply Or.inl
  intro assump_10
  have assump_44 : ((p5 ∨ p7) ∨ (True ∨ p7)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_14 := assump_7 assump_44
  apply False.elim assump_14
  intro assump_18
  intro assump_19
  cases assump_18
  case intro assump_22 assump_23 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      cases assump_25
      case inl assump_28 =>
        apply False.elim assump_28
      case inr assump_29 =>
        cases assump_23
        case intro assump_34 assump_35 =>
          have assump_45 : True := by
            apply True.intro
          let assump_40 := assump_35 assump_45
          apply False.elim assump_40


variable (p2 p1 p0 p4 : Prop)
theorem file53_34609 : (((((p4 → False) → False) → False) ∧ (((p1 → False) → (True ∧ p2)) ∧ ((True → False) ∧ (p0 ∨ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_25 : True := by
            apply True.intro
          let assump_19 := assump_10 assump_25
          apply False.elim assump_19
        case inr assump_15 =>
          apply False.elim assump_15


variable (p2 p0 p3 p6 p5 p7 p4 : Prop)
theorem file53_35246 : (((((p6 ∨ p3) ∧ (p5 ∧ False)) → ((True → True) ∨ (p4 → p7))) ∨ (((p2 → p4) → (p7 → False)) → ((p7 ∨ p3) → False))) ∨ ((((p3 ∨ p2) ∨ (True → p2)) ∧ ((p0 ∨ p3) ∨ (False ∧ True))) → False)) := by
  apply Or.inl
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


variable (p2 p5 p6 p4 p3 p1 : Prop)
theorem file53_35858 : (((((p1 ∨ False) ∧ (False ∧ p4)) ∧ ((p5 ∧ True) ∨ (p4 → False))) ∧ (((p1 → True) → False) → ((p6 → p1) ∨ (p2 ∧ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_9 =>
          apply False.elim assump_9


variable (p3 p5 p6 p0 p4 : Prop)
theorem file53_36455 : ((((((p6 → p3) ∧ (False ∧ p0)) → False) ∨ (((p5 → p6) ∨ (p6 ∨ p5)) → ((True → False) → (p4 ∧ p4)))) → False) → False) := by
  intro assump_29
  have assump_45 : ((((p6 → p3) ∧ (False ∧ p0)) → False) ∨ (((p5 → p6) ∨ (p6 ∨ p5)) → ((True → False) → (p4 ∧ p4)))) := by
    apply Or.inl
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      cases assump_35
      case intro assump_38 assump_39 =>
        apply False.elim assump_38
  let assump_32 := assump_29 assump_45
  apply False.elim assump_32


variable (p0 p6 p5 p3 p2 p4 : Prop)
theorem file53_37040 : (((((True → False) ∨ (p3 ∨ p2)) → ((p3 → False) → (True ∨ p6))) ∨ (((p2 → False) ∨ (True ∧ p4)) → ((True ∧ p2) ∨ (p3 → True)))) → ((((False ∧ True) ∧ (p2 ∨ p5)) ∧ ((p0 ∧ p6) ∧ (True → p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p0 p5 p2 p6 p1 p3 p7 : Prop)
theorem file53_37542 : (((((True ∧ p3) → False) ∧ ((p2 → p6) ∧ (p1 → p7))) ∨ (((p2 ∨ True) → False) ∧ ((False ∨ p0) → (p2 → False)))) → ((((p6 ∧ p3) → False) ∨ ((p2 ∧ p2) → False)) ∨ (((True ∨ p5) ∨ (p3 ∧ p5)) ∨ ((p2 → False) ∨ (p1 → p3))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          have assump_49 : (True ∧ p3) := by
            apply And.intro
            apply True.intro
            exact assump_16
          let assump_25 := assump_4 assump_49
          apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case intro assump_29 assump_30 =>
      apply Or.inl
      apply Or.inl
      intro assump_35
      cases assump_35
      case intro assump_36 assump_37 =>
        have assump_50 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_45 := assump_29 assump_50
        apply False.elim assump_45


variable (p5 p1 p4 p0 p3 : Prop)
theorem file53_38715 : (((((p1 ∧ p1) → False) ∧ ((p1 ∧ p0) → (p0 → False))) → (((p4 → p4) → False) → False)) ∨ ((((p3 → p5) → False) ∨ ((p3 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_20 : (p4 → p4) := by
      intro assump_14
      exact assump_14
    let assump_13 := assump_2 assump_20
    apply False.elim assump_13


variable (p6 p2 p7 : Prop)
theorem file53_39170 : (((((False → p6) ∨ (p2 → True)) → False) ∧ (((p7 ∧ True) ∨ (False ∧ False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((False → p6) ∨ (p2 → True)) := by
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p2 p3 p0 p1 p5 p7 p6 : Prop)
theorem file53_39601 : ((((((p3 ∧ p0) → (p1 → True)) → False) ∨ (((p2 ∧ True) → (p2 → True)) → False)) ∧ ((((p7 ∨ p0) ∧ (p6 ∧ p6)) ∨ ((False ∧ p5) ∨ (p6 → True))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_30 : (((p7 ∨ p0) ∧ (p6 ∧ p6)) ∨ ((False ∧ p5) ∨ (p6 → True))) := by
        apply Or.inr
        apply Or.inr
        intro assump_17
        apply True.intro
      let assump_16 := assump_9 assump_30
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_31 : (((p7 ∨ p0) ∧ (p6 ∧ p6)) ∨ ((False ∧ p5) ∨ (p6 → True))) := by
        apply Or.inr
        apply Or.inr
        intro assump_26
        apply True.intro
      let assump_25 := assump_9 assump_31
      apply False.elim assump_25


variable (p6 p7 p0 p3 p5 p1 : Prop)
theorem file53_40469 : ((((((p6 → p6) ∨ (False ∧ p1)) ∨ ((p5 → p7) → False)) ∨ (((False ∧ p3) → False) ∧ ((p1 → False) → (p7 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 → p6) ∨ (False ∧ p1)) ∨ ((p5 → p7) → False)) ∨ (((False ∧ p3) → False) ∧ ((p1 → False) → (p7 ∨ p0)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p4 p2 p5 p3 p6 p0 p1 : Prop)
theorem file53_40975 : (((((p7 → False) ∧ (False → p3)) → False) → (((p0 ∧ p2) ∨ (p5 ∧ True)) ∧ ((p1 → p6) → False))) → ((((False ∨ False) ∧ (p3 → p0)) ∧ ((p0 ∧ True) ∨ (p4 ∨ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        apply False.elim assump_8


variable (p3 : Prop)
theorem file53_41477 : (((((True ∨ p3) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p3) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p3) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p5 p1 p0 p7 p4 : Prop)
theorem file53_41903 : ((((((p1 ∨ False) → False) ∨ ((p6 → False) → False)) ∨ (((p0 ∨ p4) ∨ (p1 → False)) → False)) ∧ ((((p4 ∨ p5) ∨ (p1 → False)) → ((p7 → False) → (p7 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_113 : (((p4 ∨ p5) ∨ (p1 → False)) → ((p7 → False) → (p7 → p4))) := by
          intro assump_13
          intro assump_14
          intro assump_15
          cases assump_13
          case inl assump_20 =>
            cases assump_20
            case inl assump_22 =>
              exact assump_22
            case inr assump_23 =>
              have assump_114 : p7 := by
                exact assump_15
              let assump_29 := assump_14 assump_114
              apply False.elim assump_29
          case inr assump_21 =>
            have assump_115 : p7 := by
              exact assump_15
            let assump_36 := assump_14 assump_115
            apply False.elim assump_36
        let assump_12 := assump_3 assump_113
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_116 : (((p4 ∨ p5) ∨ (p1 → False)) → ((p7 → False) → (p7 → p4))) := by
          intro assump_48
          intro assump_49
          intro assump_50
          cases assump_48
          case inl assump_55 =>
            cases assump_55
            case inl assump_57 =>
              exact assump_57
            case inr assump_58 =>
              have assump_117 : p7 := by
                exact assump_50
              let assump_64 := assump_49 assump_117
              apply False.elim assump_64
          case inr assump_56 =>
            have assump_118 : p7 := by
              exact assump_50
            let assump_71 := assump_49 assump_118
            apply False.elim assump_71
        let assump_47 := assump_3 assump_116
        apply False.elim assump_47
    case inr assump_5 =>
      have assump_119 : (((p4 ∨ p5) ∨ (p1 → False)) → ((p7 → False) → (p7 → p4))) := by
        intro assump_83
        intro assump_84
        intro assump_85
        cases assump_83
        case inl assump_90 =>
          cases assump_90
          case inl assump_92 =>
            exact assump_92
          case inr assump_93 =>
            have assump_120 : p7 := by
              exact assump_85
            let assump_99 := assump_84 assump_120
            apply False.elim assump_99
        case inr assump_91 =>
          have assump_121 : p7 := by
            exact assump_85
          let assump_106 := assump_84 assump_121
          apply False.elim assump_106
      let assump_82 := assump_3 assump_119
      apply False.elim assump_82


variable (p7 p2 p5 p1 p4 p0 p3 : Prop)
theorem file53_44681 : (((((p3 → False) ∨ (p0 → p1)) → False) ∨ (((p7 → False) ∧ (True ∧ True)) ∨ ((p4 → False) → (p5 → p3)))) → ((((True ∧ p3) ∧ (p4 → p4)) ∧ ((p7 ∧ p5) → (p2 → False))) → (((True ∨ False) ∧ (p4 ∧ p5)) ∨ ((p3 → False) → False)))) := by
  intro assump_36
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_38
    case intro assump_40 assump_41 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        cases assump_36
        case inl assump_52 =>
          apply Or.inr
          intro assump_56
          have assump_91 : p3 := by
            exact assump_43
          let assump_59 := assump_56 assump_91
          apply False.elim assump_59
        case inr assump_53 =>
          cases assump_53
          case inl assump_63 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              cases assump_66
              case intro assump_69 assump_70 =>
                apply Or.inr
                intro assump_75
                have assump_92 : p3 := by
                  exact assump_43
                let assump_78 := assump_75 assump_92
                apply False.elim assump_78
          case inr assump_64 =>
            apply Or.inr
            intro assump_84
            have assump_93 : p3 := by
              exact assump_43
            let assump_87 := assump_84 assump_93
            apply False.elim assump_87


variable (p1 p6 p5 p2 p4 : Prop)
theorem file53_46143 : ((((((p2 ∧ p1) ∨ (p5 ∨ True)) → False) ∧ (((False → False) → False) → False)) ∧ ((((p1 ∧ p4) → False) → ((True → False) → False)) ∧ (((False → False) ∨ (p6 ∨ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_23 : ((False → False) ∨ (p6 ∨ p2)) := by
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_11 assump_23
        apply False.elim assump_16


variable (p6 p4 p0 p1 p2 p5 : Prop)
theorem file53_46803 : (((((p4 ∨ False) → False) ∧ ((p4 ∧ p1) ∧ (p6 → False))) ∧ (((p4 → p1) → (p0 → True)) ∧ ((False ∧ False) ∨ (p2 ∧ p2)))) → ((((p1 ∧ p0) ∨ (p1 → False)) ∨ ((p0 → False) → (False ∧ p1))) ∨ (((p5 ∧ p0) → (p6 → p6)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
            case inr assump_23 =>
              cases assump_23
              case intro assump_28 assump_29 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                intro assump_34
                have assump_52 : (p4 ∨ False) := by
                  apply Or.inl
                  exact assump_10
                let assump_48 := assump_4 assump_52
                apply False.elim assump_48


variable (p1 p4 p7 p6 p3 p2 p5 : Prop)
theorem file53_48035 : (((((p2 ∧ p2) ∨ (p6 ∧ False)) ∨ ((True → False) → (p4 → False))) ∨ (((p4 → False) → (p2 → False)) → False)) ∨ ((((p7 ∨ p5) ∨ (p3 → False)) → False) → (((p3 ∧ p5) ∧ (p4 ∧ True)) → ((False ∨ p1) ∨ (p1 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p6 p7 p4 p0 p2 p5 p3 : Prop)
theorem file53_48508 : (((((p6 ∧ p4) → (True → False)) → ((True ∧ True) ∧ (False → False))) ∨ (((p3 ∨ p3) → (False ∨ p4)) → False)) ∨ ((((p2 ∨ p7) → (p0 ∨ p3)) ∨ ((p6 ∧ p4) ∨ (p6 ∨ p7))) ∧ (((p5 ∧ p6) → (False → p5)) ∧ ((p2 ∨ p4) ∨ (p0 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_2
  apply False.elim assump_2


variable (p6 p5 p7 : Prop)
theorem file53_48954 : ((((((True ∨ False) → False) → False) ∨ (((p6 ∨ p7) → False) ∧ ((p5 → False) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ False) → False) → False) ∨ (((p6 ∨ p7) → False) ∧ ((p5 → False) → (True → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p0 p3 p7 p6 p5 p2 p1 : Prop)
theorem file53_49532 : (((((True → False) ∨ (p6 ∧ p1)) ∨ ((p0 ∧ p6) ∨ (p3 → p5))) → (((p1 → p2) → (p7 ∨ False)) → ((False ∨ False) → False))) ∨ ((((p4 ∨ p5) ∨ (False ∧ p5)) ∨ ((p0 ∨ p5) ∨ (p1 ∧ False))) ∨ (((p3 ∧ p7) → False) ∨ ((p7 ∨ p3) ∨ (False → p5))))) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    apply False.elim assump_15
  case inr assump_16 =>
    apply False.elim assump_16


variable (p5 p0 p3 p7 p4 p2 p6 p1 : Prop)
theorem file53_50036 : (((((p6 → p0) ∧ (p1 ∨ p7)) ∨ ((p7 → p3) ∨ (p3 → p7))) ∨ (((p6 → p3) ∧ (p4 → False)) → False)) → ((((p7 ∨ p5) ∨ (p7 ∨ p7)) ∧ ((True → p4) ∧ (p1 ∧ p6))) → (((p3 → p1) ∨ (True → True)) ∨ ((p0 → p6) → (p4 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case intro assump_11 assump_12 =>
          cases assump_12
          case intro assump_15 assump_16 =>
            cases assump_1
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                cases assump_23
                case intro assump_25 assump_26 =>
                  cases assump_26
                  case inl assump_29 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_33
                    exact assump_29
                  case inr assump_30 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_38
                    exact assump_15
              case inr assump_24 =>
                cases assump_24
                case inl assump_41 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_45
                  exact assump_15
                case inr assump_42 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_50
                  exact assump_15
            case inr assump_22 =>
              apply Or.inl
              apply Or.inl
              intro assump_55
              exact assump_15
      case inr assump_8 =>
        cases assump_4
        case intro assump_60 assump_61 =>
          cases assump_61
          case intro assump_64 assump_65 =>
            cases assump_1
            case inl assump_70 =>
              cases assump_70
              case inl assump_72 =>
                cases assump_72
                case intro assump_74 assump_75 =>
                  cases assump_75
                  case inl assump_78 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_82
                    exact assump_78
                  case inr assump_79 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_87
                    exact assump_64
              case inr assump_73 =>
                cases assump_73
                case inl assump_90 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_94
                  exact assump_64
                case inr assump_91 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_99
                  exact assump_64
            case inr assump_71 =>
              apply Or.inl
              apply Or.inl
              intro assump_104
              exact assump_64
    case inr assump_6 =>
      cases assump_6
      case inl assump_107 =>
        cases assump_4
        case intro assump_111 assump_112 =>
          cases assump_112
          case intro assump_115 assump_116 =>
            cases assump_1
            case inl assump_121 =>
              cases assump_121
              case inl assump_123 =>
                cases assump_123
                case intro assump_125 assump_126 =>
                  cases assump_126
                  case inl assump_129 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_133
                    exact assump_129
                  case inr assump_130 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_138
                    exact assump_115
              case inr assump_124 =>
                cases assump_124
                case inl assump_141 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_145
                  exact assump_115
                case inr assump_142 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_150
                  exact assump_115
            case inr assump_122 =>
              apply Or.inl
              apply Or.inl
              intro assump_155
              exact assump_115
      case inr assump_108 =>
        cases assump_4
        case intro assump_160 assump_161 =>
          cases assump_161
          case intro assump_164 assump_165 =>
            cases assump_1
            case inl assump_170 =>
              cases assump_170
              case inl assump_172 =>
                cases assump_172
                case intro assump_174 assump_175 =>
                  cases assump_175
                  case inl assump_178 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_182
                    exact assump_178
                  case inr assump_179 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_187
                    exact assump_164
              case inr assump_173 =>
                cases assump_173
                case inl assump_190 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_194
                  exact assump_164
                case inr assump_191 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_199
                  exact assump_164
            case inr assump_171 =>
              apply Or.inl
              apply Or.inl
              intro assump_204
              exact assump_164


variable (p2 p0 p6 p5 p1 p7 p3 : Prop)
theorem file53_55827 : (((((p0 → False) → (False ∨ p0)) ∧ ((False ∧ p1) ∧ (p6 → p5))) → (((p7 → False) → False) ∧ ((p2 → False) → (p0 ∨ p2)))) ∧ ((((False → p5) → False) → False) ∨ (((p6 → p7) → (p0 ∧ True)) ∧ ((p3 ∨ p0) ∨ (False → False))))) := by
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  intro assump_15
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  apply Or.inl
  intro assump_28
  have assump_38 : (False → p5) := by
    intro assump_32
    apply False.elim assump_32
  let assump_31 := assump_28 assump_38
  apply False.elim assump_31


variable (p7 p2 p3 p0 p4 p6 : Prop)
theorem file53_56802 : (((((p0 → p0) ∧ (p4 ∧ p2)) ∧ ((p3 → False) ∧ (p3 ∨ p4))) ∧ (((True → False) ∧ (p2 ∧ False)) ∧ ((False → False) ∨ (True → True)))) → ((((False → p6) ∨ (p7 → p3)) ∨ ((p3 ∨ p0) ∨ (p3 ∧ p2))) → (((p6 → False) ∨ (p7 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_1
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_17
                case intro assump_28 assump_29 =>
                  cases assump_29
                  case inl assump_32 =>
                    cases assump_15
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case intro assump_38 assump_39 =>
                        cases assump_39
                        case intro assump_42 assump_43 =>
                          apply False.elim assump_43
                  case inr assump_33 =>
                    cases assump_15
                    case intro assump_50 assump_51 =>
                      cases assump_50
                      case intro assump_52 assump_53 =>
                        cases assump_53
                        case intro assump_56 assump_57 =>
                          apply False.elim assump_57
      case inr assump_11 =>
        cases assump_1
        case intro assump_64 assump_65 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              cases assump_69
              case intro assump_72 assump_73 =>
                cases assump_67
                case intro assump_78 assump_79 =>
                  cases assump_79
                  case inl assump_82 =>
                    cases assump_65
                    case intro assump_86 assump_87 =>
                      cases assump_86
                      case intro assump_88 assump_89 =>
                        cases assump_89
                        case intro assump_92 assump_93 =>
                          apply False.elim assump_93
                  case inr assump_83 =>
                    cases assump_65
                    case intro assump_100 assump_101 =>
                      cases assump_100
                      case intro assump_102 assump_103 =>
                        cases assump_103
                        case intro assump_106 assump_107 =>
                          apply False.elim assump_107
    case inr assump_9 =>
      cases assump_9
      case inl assump_112 =>
        cases assump_112
        case inl assump_114 =>
          cases assump_1
          case intro assump_118 assump_119 =>
            cases assump_118
            case intro assump_120 assump_121 =>
              cases assump_120
              case intro assump_122 assump_123 =>
                cases assump_123
                case intro assump_126 assump_127 =>
                  cases assump_121
                  case intro assump_132 assump_133 =>
                    cases assump_133
                    case inl assump_136 =>
                      cases assump_119
                      case intro assump_140 assump_141 =>
                        cases assump_140
                        case intro assump_142 assump_143 =>
                          cases assump_143
                          case intro assump_146 assump_147 =>
                            apply False.elim assump_147
                    case inr assump_137 =>
                      cases assump_119
                      case intro assump_154 assump_155 =>
                        cases assump_154
                        case intro assump_156 assump_157 =>
                          cases assump_157
                          case intro assump_160 assump_161 =>
                            apply False.elim assump_161
        case inr assump_115 =>
          cases assump_1
          case intro assump_168 assump_169 =>
            cases assump_168
            case intro assump_170 assump_171 =>
              cases assump_170
              case intro assump_172 assump_173 =>
                cases assump_173
                case intro assump_176 assump_177 =>
                  cases assump_171
                  case intro assump_182 assump_183 =>
                    cases assump_183
                    case inl assump_186 =>
                      cases assump_169
                      case intro assump_190 assump_191 =>
                        cases assump_190
                        case intro assump_192 assump_193 =>
                          cases assump_193
                          case intro assump_196 assump_197 =>
                            apply False.elim assump_197
                    case inr assump_187 =>
                      cases assump_169
                      case intro assump_204 assump_205 =>
                        cases assump_204
                        case intro assump_206 assump_207 =>
                          cases assump_207
                          case intro assump_210 assump_211 =>
                            apply False.elim assump_211
      case inr assump_113 =>
        cases assump_113
        case intro assump_216 assump_217 =>
          cases assump_1
          case intro assump_222 assump_223 =>
            cases assump_222
            case intro assump_224 assump_225 =>
              cases assump_224
              case intro assump_226 assump_227 =>
                cases assump_227
                case intro assump_230 assump_231 =>
                  cases assump_225
                  case intro assump_236 assump_237 =>
                    cases assump_237
                    case inl assump_240 =>
                      cases assump_223
                      case intro assump_244 assump_245 =>
                        cases assump_244
                        case intro assump_246 assump_247 =>
                          cases assump_247
                          case intro assump_250 assump_251 =>
                            apply False.elim assump_251
                    case inr assump_241 =>
                      cases assump_223
                      case intro assump_258 assump_259 =>
                        cases assump_258
                        case intro assump_260 assump_261 =>
                          cases assump_261
                          case intro assump_264 assump_265 =>
                            apply False.elim assump_265
  case inr assump_5 =>
    cases assump_2
    case inl assump_272 =>
      cases assump_272
      case inl assump_274 =>
        cases assump_1
        case intro assump_278 assump_279 =>
          cases assump_278
          case intro assump_280 assump_281 =>
            cases assump_280
            case intro assump_282 assump_283 =>
              cases assump_283
              case intro assump_286 assump_287 =>
                cases assump_281
                case intro assump_292 assump_293 =>
                  cases assump_293
                  case inl assump_296 =>
                    cases assump_279
                    case intro assump_300 assump_301 =>
                      cases assump_300
                      case intro assump_302 assump_303 =>
                        cases assump_303
                        case intro assump_306 assump_307 =>
                          apply False.elim assump_307
                  case inr assump_297 =>
                    cases assump_279
                    case intro assump_314 assump_315 =>
                      cases assump_314
                      case intro assump_316 assump_317 =>
                        cases assump_317
                        case intro assump_320 assump_321 =>
                          apply False.elim assump_321
      case inr assump_275 =>
        cases assump_1
        case intro assump_328 assump_329 =>
          cases assump_328
          case intro assump_330 assump_331 =>
            cases assump_330
            case intro assump_332 assump_333 =>
              cases assump_333
              case intro assump_336 assump_337 =>
                cases assump_331
                case intro assump_342 assump_343 =>
                  cases assump_343
                  case inl assump_346 =>
                    cases assump_329
                    case intro assump_350 assump_351 =>
                      cases assump_350
                      case intro assump_352 assump_353 =>
                        cases assump_353
                        case intro assump_356 assump_357 =>
                          apply False.elim assump_357
                  case inr assump_347 =>
                    cases assump_329
                    case intro assump_364 assump_365 =>
                      cases assump_364
                      case intro assump_366 assump_367 =>
                        cases assump_367
                        case intro assump_370 assump_371 =>
                          apply False.elim assump_371
    case inr assump_273 =>
      cases assump_273
      case inl assump_376 =>
        cases assump_376
        case inl assump_378 =>
          cases assump_1
          case intro assump_382 assump_383 =>
            cases assump_382
            case intro assump_384 assump_385 =>
              cases assump_384
              case intro assump_386 assump_387 =>
                cases assump_387
                case intro assump_390 assump_391 =>
                  cases assump_385
                  case intro assump_396 assump_397 =>
                    cases assump_397
                    case inl assump_400 =>
                      cases assump_383
                      case intro assump_404 assump_405 =>
                        cases assump_404
                        case intro assump_406 assump_407 =>
                          cases assump_407
                          case intro assump_410 assump_411 =>
                            apply False.elim assump_411
                    case inr assump_401 =>
                      cases assump_383
                      case intro assump_418 assump_419 =>
                        cases assump_418
                        case intro assump_420 assump_421 =>
                          cases assump_421
                          case intro assump_424 assump_425 =>
                            apply False.elim assump_425
        case inr assump_379 =>
          cases assump_1
          case intro assump_432 assump_433 =>
            cases assump_432
            case intro assump_434 assump_435 =>
              cases assump_434
              case intro assump_436 assump_437 =>
                cases assump_437
                case intro assump_440 assump_441 =>
                  cases assump_435
                  case intro assump_446 assump_447 =>
                    cases assump_447
                    case inl assump_450 =>
                      cases assump_433
                      case intro assump_454 assump_455 =>
                        cases assump_454
                        case intro assump_456 assump_457 =>
                          cases assump_457
                          case intro assump_460 assump_461 =>
                            apply False.elim assump_461
                    case inr assump_451 =>
                      cases assump_433
                      case intro assump_468 assump_469 =>
                        cases assump_468
                        case intro assump_470 assump_471 =>
                          cases assump_471
                          case intro assump_474 assump_475 =>
                            apply False.elim assump_475
      case inr assump_377 =>
        cases assump_377
        case intro assump_480 assump_481 =>
          cases assump_1
          case intro assump_486 assump_487 =>
            cases assump_486
            case intro assump_488 assump_489 =>
              cases assump_488
              case intro assump_490 assump_491 =>
                cases assump_491
                case intro assump_494 assump_495 =>
                  cases assump_489
                  case intro assump_500 assump_501 =>
                    cases assump_501
                    case inl assump_504 =>
                      cases assump_487
                      case intro assump_508 assump_509 =>
                        cases assump_508
                        case intro assump_510 assump_511 =>
                          cases assump_511
                          case intro assump_514 assump_515 =>
                            apply False.elim assump_515
                    case inr assump_505 =>
                      cases assump_487
                      case intro assump_522 assump_523 =>
                        cases assump_522
                        case intro assump_524 assump_525 =>
                          cases assump_525
                          case intro assump_528 assump_529 =>
                            apply False.elim assump_529


variable (p0 p7 p5 p6 p1 : Prop)
theorem file53_70142 : ((((((p7 → False) ∧ (p5 ∧ p6)) → ((p0 → False) → (p7 → False))) ∨ (((p6 ∨ False) ∧ (p5 ∧ p7)) → ((p1 → False) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p7 → False) ∧ (p5 ∧ p6)) → ((p0 → False) → (p7 → False))) ∨ (((p6 ∨ False) ∧ (p5 ∧ p7)) → ((p1 → False) ∨ (p0 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        have assump_32 : p7 := by
          exact assump_7
        let assump_24 := assump_12 assump_32
        apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p3 p4 p2 p6 : Prop)
theorem file53_70913 : ((((((p3 ∨ p2) ∧ (p4 → p2)) ∧ ((False ∨ p6) ∧ (p6 → False))) → False) → False) → False) := by
  intro assump_10
  have assump_60 : ((((p3 ∨ p2) ∧ (p4 → p2)) ∧ ((False ∨ p6) ∧ (p6 → False))) → False) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_17
        case inl assump_19 =>
          cases assump_16
          case intro assump_25 assump_26 =>
            cases assump_25
            case inl assump_27 =>
              apply False.elim assump_27
            case inr assump_28 =>
              have assump_61 : p6 := by
                exact assump_28
              let assump_35 := assump_26 assump_61
              apply False.elim assump_35
        case inr assump_20 =>
          cases assump_16
          case intro assump_43 assump_44 =>
            cases assump_43
            case inl assump_45 =>
              apply False.elim assump_45
            case inr assump_46 =>
              have assump_62 : p6 := by
                exact assump_46
              let assump_53 := assump_44 assump_62
              apply False.elim assump_53
  let assump_13 := assump_10 assump_60
  apply False.elim assump_13


variable (p2 p0 p5 p3 p1 p4 p7 p6 : Prop)
theorem file53_72218 : (((((p1 ∧ p5) ∧ (False → False)) ∨ ((False → True) ∨ (p2 → p4))) ∧ (((p4 ∧ p4) → False) → ((False → False) ∧ (p5 → p5)))) ∨ ((((p1 → False) ∧ (False ∧ p6)) ∧ ((p0 → p0) ∨ (p2 ∧ True))) ∧ (((p2 ∧ p3) ∧ (p7 → p1)) → ((p0 → False) ∧ (p5 → False))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply True.intro
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  exact assump_6


variable (p1 p7 : Prop)
theorem file53_72732 : (((((p1 → False) → False) → False) ∧ (((p1 ∨ True) ∨ (p7 → p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p1 ∨ True) ∨ (p7 → p1)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p1 p7 p4 p0 p2 : Prop)
theorem file53_73132 : ((((((p7 → False) → (p4 ∨ True)) → False) → (((p2 ∧ True) ∨ (p4 ∧ p0)) ∨ ((p7 → False) → (p3 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 → False) → (p4 ∨ True)) → False) → (((p2 ∧ True) ∨ (p4 ∧ p0)) ∨ ((p7 → False) → (p3 ∨ p1)))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_23 : ((p7 → False) → (p4 ∨ True)) := by
      intro assump_13
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p6 p3 p4 p0 p5 p1 : Prop)
theorem file53_73774 : (((((p0 ∨ p6) ∧ (p1 → p4)) → False) ∧ (((p0 → False) → False) ∧ ((p5 ∧ p1) → (p7 → True)))) → ((((p0 ∧ p0) → False) → False) ∨ (((True ∨ p1) → (False ∧ p3)) ∧ ((p7 ∧ p6) → (p0 ∧ False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_29 : (p0 → False) := by
        intro assump_18
        have assump_30 : (p0 ∧ p0) := by
          apply And.intro
          exact assump_18
          exact assump_18
        let assump_22 := assump_12 assump_30
        apply False.elim assump_22
      let assump_17 := assump_6 assump_29
      apply False.elim assump_17


variable (p5 p1 p2 p7 p4 p0 p3 : Prop)
theorem file53_74536 : (((((True → False) → (p1 → p3)) → False) → (((p1 → p0) → False) ∨ ((p7 → True) ∧ (p0 ∨ p5)))) ∨ ((((p2 → False) ∨ (False → False)) → False) ∨ (((True ∧ p4) ∧ (p7 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_22 : ((True → False) → (p1 → p3)) := by
    intro assump_9
    intro assump_10
    have assump_23 : True := by
      apply True.intro
    let assump_15 := assump_9 assump_23
    apply False.elim assump_15
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8


variable (p4 p1 p3 p0 p7 p5 p2 : Prop)
theorem file53_75135 : (((((p7 → False) → (p5 ∨ p0)) → ((False ∨ p4) → False)) → (((p2 ∧ p1) ∧ (p7 ∧ p7)) → ((True → False) → (False ∨ p7)))) ∨ ((((p4 ∧ True) ∧ (p4 ∨ p0)) → False) ∨ (((False ∧ p3) ∨ (p4 ∧ True)) ∨ ((p0 ∨ p7) → (p0 → p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply Or.inr
        exact assump_15


variable (p4 p7 p5 p3 p1 p6 p2 p0 : Prop)
theorem file53_75704 : (((((p1 → False) ∧ (p5 ∧ p1)) ∧ ((p2 ∨ p4) ∧ (p5 → p5))) → (((p3 → False) → False) ∨ ((p6 → False) ∨ (p5 → p0)))) ∧ ((((p3 ∨ p3) ∨ (p6 ∨ p2)) → False) → (((p1 ∨ True) → False) → ((p5 → p7) → False)))) := by
  apply And.intro
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_11
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            apply Or.inl
            intro assump_30
            have assump_74 : p1 := by
              exact assump_17
            let assump_39 := assump_12 assump_74
            apply False.elim assump_39
          case inr assump_25 =>
            apply Or.inl
            intro assump_47
            have assump_75 : p1 := by
              exact assump_17
            let assump_56 := assump_12 assump_75
            apply False.elim assump_56
  intro assump_60
  intro assump_61
  intro assump_62
  have assump_76 : (p1 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_70 := assump_61 assump_76
  apply False.elim assump_70


variable (p7 p4 p3 p5 p6 p0 : Prop)
theorem file53_76950 : (((((True ∨ True) → (True → False)) → ((p5 ∨ p3) ∧ (p5 ∨ p6))) ∧ (((p7 → False) → (p7 → False)) → False)) → ((((False → False) → (p6 ∨ p5)) ∧ ((False → False) → False)) → (((p6 → False) → (p6 ∧ True)) → ((p0 ∧ p4) ∨ (p7 ∨ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      have assump_32 : ((p7 → False) → (p7 → False)) := by
        intro assump_19
        intro assump_20
        have assump_33 : p7 := by
          exact assump_20
        let assump_25 := assump_19 assump_33
        apply False.elim assump_25
      let assump_18 := assump_13 assump_32
      apply False.elim assump_18


variable (p5 p3 p6 p1 p0 p7 : Prop)
theorem file53_77728 : (((((p6 ∨ False) → False) → ((p3 → p7) → False)) ∧ (((p1 ∧ p3) → False) ∧ ((p0 ∧ False) ∧ (p3 → p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13


variable (p0 p7 p6 p1 p5 p2 p4 : Prop)
theorem file53_78196 : (((((p6 → False) → (p7 ∨ p5)) → ((p2 → p6) → (p5 ∧ p7))) ∧ (((p7 → True) ∧ (p2 → p2)) → False)) → ((((p1 → False) ∧ (p0 → p2)) ∧ ((False → p4) ∨ (p2 ∨ p2))) ∧ (((p0 → p0) → False) ∧ ((p1 ∧ p4) → False)))) := by
  intro assump_12
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    have assump_94 : ((p7 → True) ∧ (p2 → p2)) := by
      apply And.intro
      intro assump_23
      apply True.intro
      intro assump_24
      exact assump_24
    let assump_22 := assump_17 assump_94
    apply False.elim assump_22
  intro assump_30
  cases assump_12
  case intro assump_33 assump_34 =>
    have assump_95 : ((p7 → True) ∧ (p2 → p2)) := by
      apply And.intro
      intro assump_40
      apply True.intro
      intro assump_41
      exact assump_41
    let assump_39 := assump_34 assump_95
    apply False.elim assump_39
  cases assump_12
  case intro assump_47 assump_48 =>
    apply Or.inl
    intro assump_53
    apply False.elim assump_53
  apply And.intro
  intro assump_56
  cases assump_12
  case intro assump_59 assump_60 =>
    have assump_96 : ((p7 → True) ∧ (p2 → p2)) := by
      apply And.intro
      intro assump_66
      apply True.intro
      intro assump_67
      exact assump_67
    let assump_65 := assump_60 assump_96
    apply False.elim assump_65
  intro assump_73
  cases assump_73
  case intro assump_74 assump_75 =>
    cases assump_12
    case intro assump_80 assump_81 =>
      have assump_97 : ((p7 → True) ∧ (p2 → p2)) := by
        apply And.intro
        intro assump_87
        apply True.intro
        intro assump_88
        exact assump_88
      let assump_86 := assump_81 assump_97
      apply False.elim assump_86


variable (p3 p4 p1 p6 p2 p7 : Prop)
theorem file53_79985 : (((((True ∨ p3) ∨ (False ∨ p1)) → False) ∧ (((p6 ∧ True) ∨ (p7 ∨ p7)) ∧ ((p2 ∧ p1) ∧ (p4 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
      case inr assump_9 =>
        cases assump_9
        case inl assump_30 =>
          cases assump_7
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              cases assump_35
              case intro assump_42 assump_43 =>
                apply False.elim assump_43
        case inr assump_31 =>
          cases assump_7
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_51
              case intro assump_58 assump_59 =>
                apply False.elim assump_59


variable (p5 p2 p1 p7 p4 p0 : Prop)
theorem file53_81299 : (((((False ∨ True) → False) ∨ ((p0 ∧ True) → False)) ∨ (((p1 → True) → (False → False)) → False)) → ((((p4 ∨ p2) → False) ∧ ((p5 ∨ True) → False)) → (((True → False) ∨ (True → False)) ∨ ((p7 → p1) → False)))) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_7
    case inl assump_15 =>
      cases assump_15
      case inl assump_17 =>
        apply Or.inl
        apply Or.inl
        intro assump_21
        have assump_51 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_24 := assump_17 assump_51
        apply False.elim assump_24
      case inr assump_18 =>
        apply Or.inl
        apply Or.inl
        intro assump_30
        have assump_52 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_34 := assump_10 assump_52
        apply False.elim assump_34
    case inr assump_16 =>
      apply Or.inl
      apply Or.inl
      intro assump_40
      have assump_53 : ((p1 → True) → (False → False)) := by
        intro assump_44
        intro assump_45
        apply False.elim assump_45
      let assump_43 := assump_16 assump_53
      apply False.elim assump_43


variable (p1 p2 p6 p3 p0 : Prop)
theorem file53_82567 : (((((p0 → False) → (p1 → False)) → False) → False) → ((((p6 ∧ p3) ∨ (True → False)) → ((p1 → p0) → (p6 ∨ True))) ∨ (((p1 ∧ p2) ∧ (p0 ∧ p3)) → ((p3 ∧ p2) ∨ (p2 ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply Or.inl
      exact assump_10
  case inr assump_9 =>
    apply Or.inr
    apply True.intro


variable (p2 p0 p3 p1 p6 p7 : Prop)
theorem file53_83067 : ((((((p1 ∨ p3) ∧ (p0 → False)) ∨ ((p7 → p6) ∨ (p3 ∧ p2))) → (((True ∨ True) ∨ (p2 ∨ p1)) ∨ ((p3 ∨ p0) ∨ (True ∧ p2)))) → False) → False) := by
  intro assump_21
  have assump_53 : ((((p1 ∨ p3) ∧ (p0 → False)) ∨ ((p7 → p6) ∨ (p3 ∧ p2))) → (((True ∨ True) ∨ (p2 ∨ p1)) ∨ ((p3 ∨ p0) ∨ (True ∧ p2)))) := by
    intro assump_25
    cases assump_25
    case inl assump_26 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_28
        case inl assump_30 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_31 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
    case inr assump_27 =>
      cases assump_27
      case inl assump_40 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_41 =>
        cases assump_41
        case intro assump_44 assump_45 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_24 := assump_21 assump_53
  apply False.elim assump_24


variable (p6 p7 p4 p3 p2 : Prop)
theorem file53_84253 : ((((((p2 → False) → False) → ((False ∧ p7) ∧ (False ∨ True))) ∨ (((p6 ∨ p4) ∧ (True ∨ False)) → False)) ∧ ((((True ∨ p2) ∧ (True ∨ p7)) ∨ ((p3 → False) ∨ (True → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_22 : (((True ∨ p2) ∧ (True ∨ p7)) ∨ ((p3 → False) ∨ (True → False))) := by
        apply Or.inl
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_22
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_23 : (((True ∨ p2) ∧ (True ∨ p7)) ∨ ((p3 → False) ∨ (True → False))) := by
        apply Or.inl
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_18 := assump_3 assump_23
      apply False.elim assump_18


variable (p3 p1 : Prop)
theorem file53_85244 : ((((((p1 ∧ True) ∨ (p3 ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∧ True) ∨ (p3 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p1 ∧ True) ∨ (p3 ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p5 p3 p1 p0 p4 p6 p2 : Prop)
theorem file53_85743 : (((((False → p7) ∨ (p0 ∧ True)) ∨ ((p7 → True) ∧ (p4 ∧ p3))) ∨ (((True → p7) ∨ (p5 → False)) ∨ ((p4 → p3) → (p2 → p2)))) ∨ ((((p1 → False) ∨ (p6 ∨ False)) → ((p1 ∧ p3) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p0 p1 p4 : Prop)
theorem file53_86093 : (((((False ∧ p1) → False) ∨ ((p0 → p4) ∧ (p4 → p4))) → False) → False) := by
  intro assump_1
  have assump_13 : (((False ∧ p1) → False) ∨ ((p0 → p4) ∧ (p4 → p4))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p0 p4 p1 p6 p5 p3 : Prop)
theorem file53_86514 : (((((p6 → False) ∧ (True → False)) ∧ ((p6 ∧ p3) → False)) → False) ∨ ((((p1 ∨ False) ∧ (p6 ∨ True)) → ((p4 → p5) ∨ (p5 ∧ p5))) ∨ (((p2 → False) → False) → ((p1 ∨ p0) ∨ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_17 : True := by
        apply True.intro
      let assump_13 := assump_5 assump_17
      apply False.elim assump_13


variable (p7 p6 p3 p1 p4 p5 p2 : Prop)
theorem file53_87040 : (((((False ∧ p1) → False) ∨ ((False → False) → (p6 ∧ p5))) ∨ (((False ∨ p3) → (p1 → p3)) → ((p2 → p7) → (p7 → False)))) ∨ ((((False ∧ p4) ∧ (False → False)) ∨ ((True → False) → (p7 ∧ p1))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p5 p4 p3 : Prop)
theorem file53_87439 : ((((((False → False) → False) ∧ ((p4 ∧ p5) ∨ (p3 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_40 : ((((False → False) → False) ∧ ((p4 ∧ p5) ∨ (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_41 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_6 assump_41
          apply False.elim assump_20
      case inr assump_11 =>
        have assump_42 : (False → False) := by
          intro assump_31
          apply False.elim assump_31
        let assump_30 := assump_6 assump_42
        apply False.elim assump_30
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p4 p2 p0 p5 : Prop)
theorem file53_88365 : ((((((p0 ∨ p4) ∧ (True → False)) → False) ∨ (((p2 ∨ p5) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 ∨ p4) ∧ (True → False)) → False) ∨ (((p2 ∨ p5) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : True := by
          apply True.intro
        let assump_14 := assump_7 assump_30
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_31 : True := by
          apply True.intro
        let assump_22 := assump_7 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p3 p7 p2 p6 p0 p4 p5 : Prop)
theorem file53_89157 : (((((p7 ∨ False) ∧ (p6 → p3)) ∧ ((p5 ∧ p0) → (p4 → False))) → False) → ((((False ∧ p6) → (False → p2)) ∨ ((p6 → False) ∧ (False → False))) ∨ (((True ∧ p3) ∧ (p3 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p4 p5 p1 p6 p7 p3 p0 : Prop)
theorem file53_89517 : ((((((False → p7) ∧ (p1 → p4)) → False) ∧ (((p1 → False) → (False → False)) ∨ ((p1 → p1) ∧ (p6 → False)))) ∧ ((((p0 ∧ p3) → (False → p7)) ∧ ((p3 ∨ p3) ∧ (False ∧ p5))) ∧ (((p6 ∨ p1) ∨ (p3 ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
              case inr assump_21 =>
                cases assump_19
                case intro assump_30 assump_31 =>
                  apply False.elim assump_30
      case inr assump_9 =>
        cases assump_9
        case intro assump_34 assump_35 =>
          cases assump_3
          case intro assump_40 assump_41 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                cases assump_46
                case inl assump_48 =>
                  cases assump_47
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_52
                case inr assump_49 =>
                  cases assump_47
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_58


variable (p4 p1 p7 p2 p0 p3 p6 p5 : Prop)
theorem file53_91227 : ((((((p3 ∨ p2) ∧ (p7 → False)) ∨ ((p6 → p5) → False)) → (((p4 → False) ∧ (False ∧ p5)) → ((p6 ∧ p4) → False))) ∧ ((((p1 ∧ False) ∧ (True → False)) ∧ ((False ∨ p6) → (p7 ∧ p7))) ∧ (((True ∨ p4) → False) ∨ ((p0 → False) → False)))) → False) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p5 p3 p7 p0 p4 p2 p1 p6 : Prop)
theorem file53_91894 : (((((False ∨ p7) → False) ∨ ((p4 ∨ p0) ∨ (p3 ∧ True))) → (((p4 → p1) ∧ (p6 ∧ p2)) → ((False ∧ p0) → (True → True)))) ∨ ((((p3 ∨ p2) ∨ (p1 → False)) ∧ ((p5 ∧ True) ∨ (p2 ∧ p4))) → (((p6 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro


variable (p0 p3 p6 p7 p5 p1 p4 : Prop)
theorem file53_92279 : (((((p7 ∨ p6) ∨ (p6 → p0)) ∧ ((p1 → p3) ∧ (p1 → False))) ∧ (((p0 ∧ p0) → (p4 → False)) → False)) → ((((False ∧ p6) ∧ (False ∧ p7)) ∧ ((p7 ∧ p6) ∨ (False ∨ p1))) → (((p0 ∧ p5) ∧ (True → False)) ∨ ((p6 ∨ p3) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p0 p4 p1 p3 p2 : Prop)
theorem file53_92800 : (((((p0 → False) ∧ (p2 → p2)) ∧ ((False ∧ p1) ∧ (False → False))) → (((p0 → False) → False) → False)) ∨ ((((p3 → True) → False) ∨ ((p4 ∨ p3) → False)) → False)) := by
  apply Or.inl
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_14
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_23


variable (p0 p1 p5 p3 p2 p4 p7 : Prop)
theorem file53_93356 : (((((p4 → p5) → (p1 ∧ False)) → ((False → False) → (p2 → False))) → (((p2 ∧ p7) ∧ (p1 ∧ p0)) → ((p2 ∨ p3) ∨ (p7 → p7)))) ∨ ((((p0 ∧ p7) ∨ (p5 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        exact assump_5


variable (p5 p2 p1 p6 p4 : Prop)
theorem file53_93871 : (((((p2 → False) ∨ (p5 ∨ p5)) ∧ ((False → p1) → False)) → (((p5 ∧ False) → (p2 → False)) → False)) ∨ ((((p5 → p4) → (p2 ∨ p6)) ∨ ((p5 → p2) → False)) ∧ (((p5 → False) ∧ (p2 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_44 : (False → p1) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_6 assump_44
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_20 =>
        have assump_45 : (False → p1) := by
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_6 assump_45
        apply False.elim assump_26
      case inr assump_21 =>
        have assump_46 : (False → p1) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_6 assump_46
        apply False.elim assump_37


variable (p4 p3 p5 p1 p7 p2 p6 : Prop)
theorem file53_94927 : (((((p7 → True) → False) → ((p2 → False) ∨ (p1 → p2))) ∧ (((p4 ∧ p5) → (False → p3)) → ((True → False) ∧ (False → False)))) → ((((p4 ∧ p7) ∧ (True ∧ p6)) → ((p7 ∨ p4) ∨ (True ∨ p6))) ∧ (((p7 → p7) → False) ∧ ((p6 → False) ∧ (True → p2))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply Or.inl
          exact assump_6
  apply And.intro
  intro assump_23
  cases assump_1
  case intro assump_26 assump_27 =>
    have assump_80 : ((p4 ∧ p5) → (False → p3)) := by
      intro assump_33
      intro assump_34
      apply False.elim assump_34
    let assump_32 := assump_27 assump_80
    let assump_37 := And.left assump_32
    have assump_81 : True := by
      apply True.intro
    let assump_38 := assump_37 assump_81
    apply False.elim assump_38
  apply And.intro
  intro assump_42
  cases assump_1
  case intro assump_45 assump_46 =>
    have assump_82 : ((p4 ∧ p5) → (False → p3)) := by
      intro assump_52
      intro assump_53
      apply False.elim assump_53
    let assump_51 := assump_46 assump_82
    let assump_56 := And.left assump_51
    have assump_83 : True := by
      apply True.intro
    let assump_57 := assump_56 assump_83
    apply False.elim assump_57
  intro assump_61
  cases assump_1
  case intro assump_64 assump_65 =>
    have assump_84 : ((p4 ∧ p5) → (False → p3)) := by
      intro assump_71
      intro assump_72
      apply False.elim assump_72
    let assump_70 := assump_65 assump_84
    let assump_75 := And.left assump_70
    have assump_85 : True := by
      apply True.intro
    let assump_76 := assump_75 assump_85
    apply False.elim assump_76


variable (p6 p3 p2 p4 p7 p0 p5 : Prop)
theorem file53_96857 : (((((p3 → False) → False) → ((p5 ∧ p4) ∧ (p5 → False))) ∧ (((p7 ∨ p6) → False) ∧ ((False → False) → False))) → ((((True → p5) → (p2 → p5)) → ((p0 ∨ p5) ∧ (p7 → False))) ∧ (((True ∧ False) ∨ (p5 ∨ True)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_93 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_10 assump_93
      apply False.elim assump_15
  intro assump_22
  cases assump_1
  case intro assump_27 assump_28 =>
    cases assump_28
    case intro assump_31 assump_32 =>
      have assump_94 : (False → False) := by
        intro assump_38
        apply False.elim assump_38
      let assump_37 := assump_32 assump_94
      apply False.elim assump_37
  intro assump_44
  cases assump_44
  case inl assump_45 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      apply False.elim assump_48
  case inr assump_46 =>
    cases assump_46
    case inl assump_53 =>
      cases assump_1
      case intro assump_57 assump_58 =>
        cases assump_58
        case intro assump_61 assump_62 =>
          have assump_95 : (False → False) := by
            intro assump_68
            apply False.elim assump_68
          let assump_67 := assump_62 assump_95
          apply False.elim assump_67
    case inr assump_54 =>
      cases assump_1
      case intro assump_76 assump_77 =>
        cases assump_77
        case intro assump_80 assump_81 =>
          have assump_96 : (False → False) := by
            intro assump_87
            apply False.elim assump_87
          let assump_86 := assump_81 assump_96
          apply False.elim assump_86


variable (p6 p1 p0 p2 p5 p4 p7 : Prop)
theorem file53_98707 : (((((p1 ∨ p7) → False) → ((p2 ∧ p7) ∧ (False ∨ p1))) ∧ (((p5 ∨ p6) ∧ (p7 → False)) ∨ ((p4 ∧ p0) → False))) → ((((False ∨ p5) → (True ∨ True)) ∧ ((p4 ∧ p7) → (p1 → True))) ∨ (((True ∧ False) → (p5 → False)) ∨ ((True → False) ∨ (True ∨ p2))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          apply Or.inl
          apply And.intro
          intro assump_20
          cases assump_20
          case inl assump_21 =>
            apply False.elim assump_21
          case inr assump_22 =>
            apply Or.inl
            apply True.intro
          intro assump_27
          intro assump_28
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply And.intro
          intro assump_33
          cases assump_33
          case inl assump_34 =>
            apply False.elim assump_34
          case inr assump_35 =>
            apply Or.inl
            apply True.intro
          intro assump_40
          intro assump_41
          apply True.intro
    case inr assump_11 =>
      apply Or.inl
      apply And.intro
      intro assump_44
      cases assump_44
      case inl assump_45 =>
        apply False.elim assump_45
      case inr assump_46 =>
        apply Or.inl
        apply True.intro
      intro assump_51
      intro assump_52
      apply True.intro


variable (p4 p1 p3 p5 : Prop)
theorem file53_100257 : (((((False ∨ True) ∨ (p3 ∧ p5)) ∨ ((False ∧ p1) ∨ (p4 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_8 : (((False ∨ True) ∨ (p3 ∧ p5)) ∨ ((False ∧ p1) ∨ (p4 ∧ p3))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p5 p4 p7 p2 p6 : Prop)
theorem file53_100640 : (((((p7 ∧ p5) ∨ (p7 ∧ p6)) → False) ∧ (((p5 ∨ False) → (p4 ∨ p2)) ∨ ((p2 → p3) ∧ (p3 ∨ p4)))) → ((((p7 → False) → False) ∧ ((p5 → False) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_51 : True := by
            apply True.intro
          let assump_23 := assump_8 assump_51
          apply False.elim assump_23
        case inr assump_18 =>
          cases assump_18
          case intro assump_27 assump_28 =>
            cases assump_28
            case inl assump_31 =>
              have assump_52 : True := by
                apply True.intro
              let assump_38 := assump_8 assump_52
              apply False.elim assump_38
            case inr assump_32 =>
              have assump_53 : True := by
                apply True.intro
              let assump_47 := assump_8 assump_53
              apply False.elim assump_47


variable (p7 p0 p6 p4 p2 : Prop)
theorem file53_101802 : ((((((p4 → True) ∨ (p6 ∨ p4)) ∨ ((p7 → p2) ∨ (p0 ∨ p4))) ∨ (((p2 → False) ∧ (False → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p4 → True) ∨ (p6 ∨ p4)) ∨ ((p7 → p2) ∨ (p0 ∨ p4))) ∨ (((p2 → False) ∧ (False → p6)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p6 p3 p7 p5 p2 : Prop)
theorem file53_102277 : ((((((p3 → False) ∨ (True ∨ True)) ∨ ((p7 → p7) → (p2 → p2))) → (((p7 → False) → (p3 → p5)) → ((True ∧ p7) → (p6 → p7)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p3 → False) ∨ (True ∨ True)) ∨ ((p7 → p7) → (p2 → p2))) → (((p7 → False) → (p3 → p5)) → ((True ∧ p7) → (p6 → p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_5
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          exact assump_12
        case inr assump_22 =>
          cases assump_22
          case inl assump_25 =>
            exact assump_12
          case inr assump_26 =>
            exact assump_12
      case inr assump_20 =>
        exact assump_12
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p7 : Prop)
theorem file53_103185 : ((((((p7 ∨ False) ∨ (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∨ False) ∨ (False → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p7 ∨ False) ∨ (False → False)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p1 p3 : Prop)
theorem file53_103695 : ((((((p5 → p5) ∨ (p3 ∧ p1)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → p5) ∨ (p3 ∧ p1)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p5 → p5) ∨ (p3 ∧ p1)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p1 p0 p2 p7 p4 p5 p6 : Prop)
theorem file53_104182 : (((((p5 ∨ p6) → (p5 ∧ p5)) ∨ ((p1 ∨ p5) ∧ (p3 ∧ p2))) → False) → ((((p4 → p0) ∨ (p0 → False)) → ((p1 ∧ p7) → (True ∨ p0))) ∨ (((p6 ∨ p2) → False) ∧ ((False → p2) → (p0 → False))))) := by
  intro assump_9
  apply Or.inl
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_12
    case inl assump_20 =>
      apply Or.inl
      apply True.intro
    case inr assump_21 =>
      apply Or.inl
      apply True.intro


variable (p6 p2 p1 p3 p7 p5 p0 p4 : Prop)
theorem file53_104713 : (((((p4 ∧ p0) ∨ (p5 ∨ p6)) ∨ ((p4 → p2) → (True ∧ p2))) ∧ (((p4 → False) ∧ (p0 ∧ p2)) ∧ ((p5 ∨ p6) ∨ (p3 → False)))) → ((((p0 ∨ True) → (p2 → p3)) → False) → (((True ∨ p5) ∨ (True ∧ p7)) ∨ ((p1 ∨ p7) ∧ (p4 ∨ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_6
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_20
              case intro assump_23 assump_24 =>
                cases assump_18
                case inl assump_29 =>
                  cases assump_29
                  case inl assump_31 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_32 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_30 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
      case inr assump_10 =>
        cases assump_10
        case inl assump_39 =>
          cases assump_6
          case intro assump_43 assump_44 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              cases assump_46
              case intro assump_49 assump_50 =>
                cases assump_44
                case inl assump_55 =>
                  cases assump_55
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
                case inr assump_56 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
        case inr assump_40 =>
          cases assump_6
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              cases assump_70
              case intro assump_73 assump_74 =>
                cases assump_68
                case inl assump_79 =>
                  cases assump_79
                  case inl assump_81 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  case inr assump_82 =>
                    apply Or.inl
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                case inr assump_80 =>
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
    case inr assump_8 =>
      cases assump_6
      case intro assump_91 assump_92 =>
        cases assump_91
        case intro assump_93 assump_94 =>
          cases assump_94
          case intro assump_97 assump_98 =>
            cases assump_92
            case inl assump_103 =>
              cases assump_103
              case inl assump_105 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              case inr assump_106 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
            case inr assump_104 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro


variable (p3 p5 p0 p2 p7 : Prop)
theorem file53_108655 : (((((p7 → p2) → False) ∧ ((p0 ∧ p2) → (p2 → False))) ∧ (((p2 ∧ p3) → (False → False)) → False)) → ((((True → False) ∨ (True → p2)) ∧ ((p2 → p5) ∨ (p2 ∨ False))) ∧ (((p5 ∨ False) ∨ (p5 ∨ p2)) → False))) := by
  intro assump_24
  apply And.intro
  apply And.intro
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      apply Or.inl
      intro assump_35
      have assump_137 : ((p2 ∧ p3) → (False → False)) := by
        intro assump_39
        intro assump_40
        apply False.elim assump_40
      let assump_38 := assump_26 assump_137
      apply False.elim assump_38
  cases assump_24
  case intro assump_46 assump_47 =>
    cases assump_46
    case intro assump_48 assump_49 =>
      apply Or.inl
      intro assump_56
      have assump_138 : ((p2 ∧ p3) → (False → False)) := by
        intro assump_61
        intro assump_62
        apply False.elim assump_62
      let assump_60 := assump_47 assump_138
      apply False.elim assump_60
  intro assump_68
  cases assump_68
  case inl assump_69 =>
    cases assump_69
    case inl assump_71 =>
      cases assump_24
      case intro assump_75 assump_76 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          have assump_139 : ((p2 ∧ p3) → (False → False)) := by
            intro assump_86
            intro assump_87
            apply False.elim assump_87
          let assump_85 := assump_76 assump_139
          apply False.elim assump_85
    case inr assump_72 =>
      apply False.elim assump_72
  case inr assump_70 =>
    cases assump_70
    case inl assump_95 =>
      cases assump_24
      case intro assump_99 assump_100 =>
        cases assump_99
        case intro assump_101 assump_102 =>
          have assump_140 : ((p2 ∧ p3) → (False → False)) := by
            intro assump_110
            intro assump_111
            apply False.elim assump_111
          let assump_109 := assump_100 assump_140
          apply False.elim assump_109
    case inr assump_96 =>
      cases assump_24
      case intro assump_119 assump_120 =>
        cases assump_119
        case intro assump_121 assump_122 =>
          have assump_141 : ((p2 ∧ p3) → (False → False)) := by
            intro assump_130
            intro assump_131
            apply False.elim assump_131
          let assump_129 := assump_120 assump_141
          apply False.elim assump_129


variable (p2 p0 p3 p4 p5 p1 p7 : Prop)
theorem file53_111123 : (((((False ∧ p4) ∧ (p1 ∧ p2)) → False) ∨ (((p3 ∧ p3) ∨ (p0 ∧ p7)) → ((True → False) ∧ (p7 ∨ p1)))) ∨ ((((p1 → False) ∨ (p0 ∧ p5)) ∧ ((p3 ∨ p2) → False)) ∨ (((p7 ∨ True) → False) ∧ ((p2 ∧ p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p1 p5 p7 p2 p0 : Prop)
theorem file53_111574 : ((((((p7 ∨ p1) → (False → p5)) ∨ ((False → p2) → (True → False))) ∨ (((p7 → False) → (True → p0)) → ((p0 ∨ False) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p7 ∨ p1) → (False → p5)) ∨ ((False → p2) → (True → False))) ∨ (((p7 → False) → (True → p0)) → ((p0 ∨ False) ∧ (p2 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p0 p5 p4 p3 p6 : Prop)
theorem file53_112129 : ((((((p3 ∧ True) ∨ (p6 ∨ p0)) → False) ∧ (((p4 ∧ p2) ∧ (p6 ∨ False)) → ((False → False) ∧ (p0 → False)))) ∧ ((((p4 → p4) ∨ (p5 → False)) ∧ ((True → False) → (p4 ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_32 : (((p4 → p4) ∨ (p5 → False)) ∧ ((True → False) → (p4 ∧ p3))) := by
        apply And.intro
        apply Or.inl
        intro assump_13
        exact assump_13
        intro assump_16
        apply And.intro
        have assump_33 : True := by
          apply True.intro
        let assump_19 := assump_16 assump_33
        apply False.elim assump_19
        have assump_34 : True := by
          apply True.intro
        let assump_25 := assump_16 assump_34
        apply False.elim assump_25
      let assump_12 := assump_3 assump_32
      apply False.elim assump_12


