variable (p6 p3 p2 p7 p4 p5 p1 p0 : Prop)
theorem file72_50 : ((((((p5 ∧ p7) → (p3 → p6)) → ((p1 ∨ True) ∨ (p7 → p5))) ∨ (((p0 ∨ p6) ∨ (p4 ∧ p3)) → False)) ∧ ((((p7 ∨ p2) ∨ (p2 → p2)) → False) ∨ (((p4 ∧ p0) → (p1 → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        have assump_64 : ((p7 ∨ p2) ∨ (p2 → p2)) := by
          apply Or.inr
          intro assump_13
          exact assump_13
        let assump_12 := assump_8 assump_64
        apply False.elim assump_12
      case inr assump_9 =>
        have assump_65 : ((p4 ∧ p0) → (p1 → p4)) := by
          intro assump_22
          intro assump_23
          cases assump_22
          case intro assump_26 assump_27 =>
            exact assump_26
        let assump_21 := assump_9 assump_65
        apply False.elim assump_21
    case inr assump_5 =>
      cases assump_3
      case inl assump_37 =>
        have assump_66 : ((p7 ∨ p2) ∨ (p2 → p2)) := by
          apply Or.inr
          intro assump_42
          exact assump_42
        let assump_41 := assump_37 assump_66
        apply False.elim assump_41
      case inr assump_38 =>
        have assump_67 : ((p4 ∧ p0) → (p1 → p4)) := by
          intro assump_51
          intro assump_52
          cases assump_51
          case intro assump_55 assump_56 =>
            exact assump_55
        let assump_50 := assump_38 assump_67
        apply False.elim assump_50


variable (p1 p2 p5 p0 p4 p6 p3 : Prop)
theorem file72_1574 : ((((((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) → False) ∧ ((((p4 ∧ p2) ∨ (p1 → False)) ∨ ((p3 → p5) ∨ (p6 ∧ True))) ∨ (((p1 ∧ p0) ∧ (False ∨ p4)) ∨ ((p4 → p3) ∧ (p6 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_145 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
            let assump_20 := assump_2 assump_145
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_146 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
            intro assump_37
            cases assump_37
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply False.elim assump_41
          let assump_36 := assump_2 assump_146
          apply False.elim assump_36
      case inr assump_9 =>
        cases assump_9
        case inl assump_49 =>
          have assump_147 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
            intro assump_55
            cases assump_55
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                apply False.elim assump_59
          let assump_54 := assump_2 assump_147
          apply False.elim assump_54
        case inr assump_50 =>
          cases assump_50
          case intro assump_67 assump_68 =>
            have assump_148 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
              intro assump_75
              cases assump_75
              case intro assump_76 assump_77 =>
                cases assump_76
                case intro assump_78 assump_79 =>
                  apply False.elim assump_79
            let assump_74 := assump_2 assump_148
            apply False.elim assump_74
    case inr assump_7 =>
      cases assump_7
      case inl assump_87 =>
        cases assump_87
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_90
            case inl assump_97 =>
              apply False.elim assump_97
            case inr assump_98 =>
              have assump_149 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
                intro assump_107
                cases assump_107
                case intro assump_108 assump_109 =>
                  cases assump_108
                  case intro assump_110 assump_111 =>
                    apply False.elim assump_111
              let assump_106 := assump_2 assump_149
              apply False.elim assump_106
      case inr assump_88 =>
        cases assump_88
        case intro assump_119 assump_120 =>
          cases assump_120
          case intro assump_123 assump_124 =>
            have assump_150 : (((p3 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p1) ∨ (False → False))) := by
              intro assump_133
              cases assump_133
              case intro assump_134 assump_135 =>
                cases assump_134
                case intro assump_136 assump_137 =>
                  apply False.elim assump_137
            let assump_132 := assump_2 assump_150
            apply False.elim assump_132


variable (p3 p2 p0 p4 p5 : Prop)
theorem file72_5390 : ((((((p3 → p5) → (p4 ∨ True)) → ((p3 → True) → (p2 ∨ p5))) → (((False → False) ∨ (p0 → False)) ∨ ((p5 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → p5) → (p4 ∨ True)) → ((p3 → True) → (p2 ∨ p5))) → (((False → False) ∨ (p0 → False)) ∨ ((p5 ∨ True) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p7 p0 : Prop)
theorem file72_5914 : ((((((False → p0) → (p7 ∧ p4)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_14
  have assump_35 : ((((False → p0) → (p7 ∧ p4)) ∧ ((False → False) → False)) → False) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      have assump_36 : (False → False) := by
        intro assump_26
        apply False.elim assump_26
      let assump_25 := assump_20 assump_36
      apply False.elim assump_25
  let assump_17 := assump_14 assump_35
  apply False.elim assump_17


variable (p4 p1 p0 p3 p6 p2 p5 p7 : Prop)
theorem file72_6509 : (((((p0 ∧ False) ∧ (True ∨ p2)) → ((p7 → p6) → False)) → False) → ((((True ∧ p4) ∨ (True ∧ p1)) → ((True ∨ p7) ∨ (p5 ∧ p2))) ∧ (((p1 ∨ True) → (p3 ∧ p2)) → ((p1 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_4 =>
    cases assump_4
    case intro assump_13 assump_14 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  intro assump_21
  intro assump_22
  have assump_45 : (((p0 ∧ False) ∧ (True ∨ p2)) → ((p7 → p6) → False)) := by
    intro assump_30
    intro assump_31
    cases assump_30
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        apply False.elim assump_37
  let assump_29 := assump_1 assump_45
  apply False.elim assump_29


variable (p2 p6 p7 p3 p1 : Prop)
theorem file72_7479 : ((((((p1 ∨ p6) → False) → ((p3 ∨ p1) ∨ (False → p7))) ∨ (((p1 → False) ∧ (p2 → p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∨ p6) → False) → ((p3 ∨ p1) ∨ (False → p7))) ∨ (((p1 → False) ∧ (p2 → p2)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p1 p7 p3 p0 p5 : Prop)
theorem file72_7958 : ((((((p0 ∨ False) ∧ (p1 → p5)) ∧ ((True → p1) → False)) → (((False ∧ p3) ∧ (p7 → False)) → ((p6 ∨ p0) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 ∨ False) ∧ (p1 → p5)) ∧ ((True → p1) → False)) → (((False ∧ p3) ∧ (p7 → False)) → ((p6 ∨ p0) ∧ (p7 ∨ True)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p1 p4 p0 p2 p5 p6 : Prop)
theorem file72_8749 : (((((p2 → False) → (False → False)) ∨ ((p4 ∨ False) → (p4 ∨ False))) ∧ (((p2 → False) → (p0 ∨ p0)) ∧ ((True → False) ∧ (True ∧ p6)))) → ((((p5 → p6) → (True → False)) ∨ ((p5 ∧ p1) ∧ (p2 ∧ p5))) ∧ (((p6 → p4) → (False ∨ p7)) → False))) := by
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
          cases assump_13
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            intro assump_23
            have assump_111 : True := by
              apply True.intro
            let assump_30 := assump_12 assump_111
            apply False.elim assump_30
    case inr assump_5 =>
      cases assump_3
      case intro assump_36 assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          cases assump_41
          case intro assump_44 assump_45 =>
            apply Or.inl
            intro assump_50
            intro assump_51
            have assump_112 : True := by
              apply True.intro
            let assump_58 := assump_40 assump_112
            apply False.elim assump_58
  intro assump_62
  cases assump_1
  case intro assump_65 assump_66 =>
    cases assump_65
    case inl assump_67 =>
      cases assump_66
      case intro assump_71 assump_72 =>
        cases assump_72
        case intro assump_75 assump_76 =>
          cases assump_76
          case intro assump_79 assump_80 =>
            have assump_113 : True := by
              apply True.intro
            let assump_86 := assump_75 assump_113
            apply False.elim assump_86
    case inr assump_68 =>
      cases assump_66
      case intro assump_92 assump_93 =>
        cases assump_93
        case intro assump_96 assump_97 =>
          cases assump_97
          case intro assump_100 assump_101 =>
            have assump_114 : True := by
              apply True.intro
            let assump_107 := assump_96 assump_114
            apply False.elim assump_107


variable (p2 p3 p7 p6 p0 p5 : Prop)
theorem file72_10945 : (((((p2 ∧ p6) ∧ (p7 → False)) ∧ ((p0 → False) → False)) ∧ (((False ∧ p3) → False) ∧ ((p2 → False) ∧ (p5 ∨ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_23
              case inl assump_26 =>
                have assump_42 : p2 := by
                  exact assump_8
                let assump_31 := assump_22 assump_42
                apply False.elim assump_31
              case inr assump_27 =>
                have assump_43 : p2 := by
                  exact assump_8
                let assump_38 := assump_22 assump_43
                apply False.elim assump_38


variable (p6 p4 p0 p3 p1 p2 p7 p5 : Prop)
theorem file72_11971 : ((((((p7 → p1) ∨ (p5 ∨ p2)) ∧ ((p1 → False) → (p6 → p2))) ∨ (((p4 ∨ p7) ∨ (p3 → False)) → False)) ∧ ((((p0 ∨ p7) ∨ (p6 ∧ p7)) ∧ ((p3 ∨ p4) ∧ (p0 ∧ False))) ∧ (((p3 ∨ False) → (p6 ∧ p3)) ∨ ((p1 → p2) ∧ (True → True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_18
                case inl assump_20 =>
                  cases assump_17
                  case intro assump_24 assump_25 =>
                    cases assump_24
                    case inl assump_26 =>
                      cases assump_25
                      case intro assump_30 assump_31 =>
                        apply False.elim assump_31
                    case inr assump_27 =>
                      cases assump_25
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_39
                case inr assump_21 =>
                  cases assump_17
                  case intro assump_46 assump_47 =>
                    cases assump_46
                    case inl assump_48 =>
                      cases assump_47
                      case intro assump_52 assump_53 =>
                        apply False.elim assump_53
                    case inr assump_49 =>
                      cases assump_47
                      case intro assump_60 assump_61 =>
                        apply False.elim assump_61
              case inr assump_19 =>
                cases assump_19
                case intro assump_66 assump_67 =>
                  cases assump_17
                  case intro assump_72 assump_73 =>
                    cases assump_72
                    case inl assump_74 =>
                      cases assump_73
                      case intro assump_78 assump_79 =>
                        apply False.elim assump_79
                    case inr assump_75 =>
                      cases assump_73
                      case intro assump_86 assump_87 =>
                        apply False.elim assump_87
        case inr assump_9 =>
          cases assump_9
          case inl assump_92 =>
            cases assump_3
            case intro assump_98 assump_99 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                cases assump_100
                case inl assump_102 =>
                  cases assump_102
                  case inl assump_104 =>
                    cases assump_101
                    case intro assump_108 assump_109 =>
                      cases assump_108
                      case inl assump_110 =>
                        cases assump_109
                        case intro assump_114 assump_115 =>
                          apply False.elim assump_115
                      case inr assump_111 =>
                        cases assump_109
                        case intro assump_122 assump_123 =>
                          apply False.elim assump_123
                  case inr assump_105 =>
                    cases assump_101
                    case intro assump_130 assump_131 =>
                      cases assump_130
                      case inl assump_132 =>
                        cases assump_131
                        case intro assump_136 assump_137 =>
                          apply False.elim assump_137
                      case inr assump_133 =>
                        cases assump_131
                        case intro assump_144 assump_145 =>
                          apply False.elim assump_145
                case inr assump_103 =>
                  cases assump_103
                  case intro assump_150 assump_151 =>
                    cases assump_101
                    case intro assump_156 assump_157 =>
                      cases assump_156
                      case inl assump_158 =>
                        cases assump_157
                        case intro assump_162 assump_163 =>
                          apply False.elim assump_163
                      case inr assump_159 =>
                        cases assump_157
                        case intro assump_170 assump_171 =>
                          apply False.elim assump_171
          case inr assump_93 =>
            cases assump_3
            case intro assump_180 assump_181 =>
              cases assump_180
              case intro assump_182 assump_183 =>
                cases assump_182
                case inl assump_184 =>
                  cases assump_184
                  case inl assump_186 =>
                    cases assump_183
                    case intro assump_190 assump_191 =>
                      cases assump_190
                      case inl assump_192 =>
                        cases assump_191
                        case intro assump_196 assump_197 =>
                          apply False.elim assump_197
                      case inr assump_193 =>
                        cases assump_191
                        case intro assump_204 assump_205 =>
                          apply False.elim assump_205
                  case inr assump_187 =>
                    cases assump_183
                    case intro assump_212 assump_213 =>
                      cases assump_212
                      case inl assump_214 =>
                        cases assump_213
                        case intro assump_218 assump_219 =>
                          apply False.elim assump_219
                      case inr assump_215 =>
                        cases assump_213
                        case intro assump_226 assump_227 =>
                          apply False.elim assump_227
                case inr assump_185 =>
                  cases assump_185
                  case intro assump_232 assump_233 =>
                    cases assump_183
                    case intro assump_238 assump_239 =>
                      cases assump_238
                      case inl assump_240 =>
                        cases assump_239
                        case intro assump_244 assump_245 =>
                          apply False.elim assump_245
                      case inr assump_241 =>
                        cases assump_239
                        case intro assump_252 assump_253 =>
                          apply False.elim assump_253
    case inr assump_5 =>
      cases assump_3
      case intro assump_260 assump_261 =>
        cases assump_260
        case intro assump_262 assump_263 =>
          cases assump_262
          case inl assump_264 =>
            cases assump_264
            case inl assump_266 =>
              cases assump_263
              case intro assump_270 assump_271 =>
                cases assump_270
                case inl assump_272 =>
                  cases assump_271
                  case intro assump_276 assump_277 =>
                    apply False.elim assump_277
                case inr assump_273 =>
                  cases assump_271
                  case intro assump_284 assump_285 =>
                    apply False.elim assump_285
            case inr assump_267 =>
              cases assump_263
              case intro assump_292 assump_293 =>
                cases assump_292
                case inl assump_294 =>
                  cases assump_293
                  case intro assump_298 assump_299 =>
                    apply False.elim assump_299
                case inr assump_295 =>
                  cases assump_293
                  case intro assump_306 assump_307 =>
                    apply False.elim assump_307
          case inr assump_265 =>
            cases assump_265
            case intro assump_312 assump_313 =>
              cases assump_263
              case intro assump_318 assump_319 =>
                cases assump_318
                case inl assump_320 =>
                  cases assump_319
                  case intro assump_324 assump_325 =>
                    apply False.elim assump_325
                case inr assump_321 =>
                  cases assump_319
                  case intro assump_332 assump_333 =>
                    apply False.elim assump_333


variable (p0 p2 p5 p7 p1 p3 p4 : Prop)
theorem file72_20491 : (((((p5 ∨ True) ∨ (p1 ∨ p2)) ∨ ((p3 ∧ p5) → (p2 ∨ p2))) → False) → ((((p0 ∨ p1) → (True → False)) ∧ ((p1 → p4) ∧ (p0 → False))) → (((p1 → False) → (p1 ∨ p4)) ∧ ((False → p7) → False)))) := by
  intro assump_10
  intro assump_11
  apply And.intro
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      have assump_50 : (((p5 ∨ True) ∨ (p1 ∨ p2)) ∨ ((p3 ∧ p5) → (p2 ∨ p2))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_27 := assump_10 assump_50
      apply False.elim assump_27
  intro assump_31
  cases assump_11
  case intro assump_34 assump_35 =>
    cases assump_35
    case intro assump_38 assump_39 =>
      have assump_51 : (((p5 ∨ True) ∨ (p1 ∨ p2)) ∨ ((p3 ∧ p5) → (p2 ∨ p2))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_46 := assump_10 assump_51
      apply False.elim assump_46


variable (p4 p7 p1 p0 p5 p6 p2 p3 : Prop)
theorem file72_21557 : (((((False → False) ∨ (False → False)) ∧ ((p7 ∧ True) → (False ∧ p2))) ∧ (((p0 → False) ∧ (p2 → False)) ∨ ((p1 → p1) → (p1 → False)))) → ((((p4 ∨ p3) → (p0 ∨ p1)) → ((False ∧ p0) → False)) ∨ (((p0 ∧ False) ∨ (p6 ∨ False)) → ((p7 → p5) → (p3 ∧ p2))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_24
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              apply False.elim assump_26
        case inr assump_17 =>
          apply Or.inl
          intro assump_32
          intro assump_33
          cases assump_33
          case intro assump_34 assump_35 =>
            apply False.elim assump_34
      case inr assump_11 =>
        cases assump_7
        case inl assump_42 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            apply Or.inl
            intro assump_50
            intro assump_51
            cases assump_51
            case intro assump_52 assump_53 =>
              apply False.elim assump_52
        case inr assump_43 =>
          apply Or.inl
          intro assump_58
          intro assump_59
          cases assump_59
          case intro assump_60 assump_61 =>
            apply False.elim assump_60


variable (p6 p5 p3 p7 p1 p2 p4 : Prop)
theorem file72_23143 : (((((True → False) → (p2 ∧ p6)) ∧ ((p1 ∨ p5) → False)) ∧ (((p1 ∧ p5) → False) ∨ ((p4 ∨ p1) → False))) → ((((False → False) ∧ (p3 ∧ p5)) ∨ ((p1 ∧ False) ∧ (p7 → p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_16
            case inl assump_23 =>
              have assump_47 : (p1 ∨ p5) := by
                apply Or.inr
                exact assump_10
              let assump_28 := assump_18 assump_47
              apply False.elim assump_28
            case inr assump_24 =>
              have assump_48 : (p1 ∨ p5) := by
                apply Or.inr
                exact assump_10
              let assump_35 := assump_18 assump_48
              apply False.elim assump_35
  case inr assump_4 =>
    cases assump_4
    case intro assump_39 assump_40 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        apply False.elim assump_42


variable (p3 p0 p4 : Prop)
theorem file72_24373 : (((((p0 ∧ True) ∨ (p0 → p0)) ∧ ((p3 ∧ False) → (p4 ∨ p3))) → False) → False) := by
  intro assump_9
  have assump_26 : (((p0 ∧ True) ∨ (p0 → p0)) ∧ ((p3 ∧ False) → (p4 ∨ p3))) := by
    apply And.intro
    apply Or.inr
    intro assump_13
    exact assump_13
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_18
  let assump_12 := assump_9 assump_26
  apply False.elim assump_12


variable (p7 p0 p2 p1 p5 p3 p6 : Prop)
theorem file72_24873 : (((((p6 → p0) → (p0 ∧ p3)) ∧ ((True ∧ p2) ∧ (p2 → False))) → False) ∨ ((((p5 → p2) → (p6 ∧ p7)) ∨ ((True → False) → (p2 ∧ p1))) ∧ (((p6 → False) ∨ (p5 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_20 : p2 := by
          exact assump_9
        let assump_16 := assump_7 assump_20
        apply False.elim assump_16


variable (p5 p0 p1 p3 p4 p6 p2 p7 : Prop)
theorem file72_25449 : (((((p2 → False) → False) ∧ ((p3 → p0) ∧ (p7 → p4))) ∨ (((p3 ∧ p5) → (p1 ∨ p1)) ∨ ((p5 → False) ∨ (p7 ∧ True)))) → ((((p6 ∧ False) ∧ (p1 → False)) ∧ ((p6 → False) → (p3 ∨ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p0 p7 p2 p1 p3 p4 p6 : Prop)
theorem file72_25938 : (((((p3 ∧ p7) ∧ (p2 → p2)) ∧ ((False → p7) → False)) → False) ∨ ((((p1 → p2) ∨ (p3 ∨ p2)) ∨ ((p1 ∨ p4) → (p1 → p0))) → (((p7 → False) ∨ (False → p2)) → ((p6 → False) → (p0 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_23 : (False → p7) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p5 p0 p1 p2 p7 p6 p4 p3 : Prop)
theorem file72_26575 : ((((((p1 → p7) ∧ (p0 → False)) ∧ ((True ∨ p2) → False)) → False) ∧ ((((p0 ∧ p0) ∧ (p6 ∨ p5)) → ((False ∨ True) ∨ (p3 → False))) ∧ (((True → False) → (True ∧ p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((True → False) → (True ∧ p4)) := by
        intro assump_13
        apply And.intro
        apply True.intro
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p0 p7 p3 p5 p1 p2 : Prop)
theorem file72_27297 : ((((((False ∧ p0) ∨ (p1 → True)) → ((False ∨ p7) → (p2 ∧ p5))) ∨ (((False ∧ False) → (p1 → False)) ∧ ((p0 → p0) ∨ (p0 ∨ p5)))) ∧ ((((True ∨ p2) ∧ (p0 → True)) ∨ ((p3 → False) ∧ (p2 → False))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      have assump_60 : (((True ∨ p2) ∧ (p0 → True)) ∨ ((p3 → False) ∧ (p2 → False))) := by
        apply Or.inl
        apply And.intro
        apply Or.inl
        apply True.intro
        intro assump_21
        apply True.intro
      let assump_20 := assump_13 assump_60
      apply False.elim assump_20
    case inr assump_15 =>
      cases assump_15
      case intro assump_25 assump_26 =>
        cases assump_26
        case inl assump_29 =>
          have assump_61 : (((True ∨ p2) ∧ (p0 → True)) ∨ ((p3 → False) ∧ (p2 → False))) := by
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply True.intro
            intro assump_36
            apply True.intro
          let assump_35 := assump_13 assump_61
          apply False.elim assump_35
        case inr assump_30 =>
          cases assump_30
          case inl assump_40 =>
            have assump_62 : (((True ∨ p2) ∧ (p0 → True)) ∨ ((p3 → False) ∧ (p2 → False))) := by
              apply Or.inl
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_47
              apply True.intro
            let assump_46 := assump_13 assump_62
            apply False.elim assump_46
          case inr assump_41 =>
            have assump_63 : (((True ∨ p2) ∧ (p0 → True)) ∨ ((p3 → False) ∧ (p2 → False))) := by
              apply Or.inl
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_56
              apply True.intro
            let assump_55 := assump_13 assump_63
            apply False.elim assump_55


variable (p5 p1 p3 p0 p6 p4 : Prop)
theorem file72_29326 : ((((((p4 ∧ p4) ∧ (p3 → False)) → ((True ∧ p6) → (False → p5))) ∨ (((p0 ∨ p4) ∧ (False ∧ p1)) → False)) → ((((False ∧ p5) → False) ∨ ((p1 → False) → False)) → False)) → False) := by
  intro assump_1
  have assump_19 : ((((p4 ∧ p4) ∧ (p3 → False)) → ((True ∧ p6) → (False → p5))) ∨ (((p0 ∨ p4) ∧ (False ∧ p1)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_19
  have assump_20 : (((False ∧ p5) → False) ∨ ((p1 → False) → False)) := by
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_10 := assump_4 assump_20
  apply False.elim assump_10


variable (p7 p6 p0 p1 : Prop)
theorem file72_30115 : (((((p1 ∧ p0) → (False → False)) ∨ ((p1 ∨ p7) → (p6 → p6))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p1 ∧ p0) → (False → False)) ∨ ((p1 ∨ p7) → (p6 → p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p1 p2 p4 p7 p3 p5 : Prop)
theorem file72_30512 : ((((((p3 ∧ p1) ∧ (p5 ∨ p4)) → ((True ∨ p2) ∧ (p0 ∨ p0))) → (((True ∧ p2) → False) → ((p2 ∨ True) ∨ (p3 → p4)))) ∧ ((((p7 → p3) → False) → False) ∧ (((p0 → False) → (p0 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : ((p0 → False) → (p0 → False)) := by
        intro assump_13
        intro assump_14
        have assump_27 : p0 := by
          exact assump_14
        let assump_19 := assump_13 assump_27
        apply False.elim assump_19
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12


variable (p3 p2 p4 p7 p1 p0 p6 : Prop)
theorem file72_31224 : (((((True ∨ False) ∧ (True → False)) ∨ ((p0 → False) ∧ (p1 ∨ p0))) ∧ (((p6 ∧ p0) ∨ (p6 → False)) → ((p4 → False) ∧ (p2 → p1)))) → ((((False → False) → False) → ((p7 → False) ∧ (p0 → False))) → (((p3 → False) → (p4 → True)) ∨ ((p3 ∧ p1) ∨ (p3 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          apply Or.inl
          intro assump_19
          intro assump_20
          apply True.intro
        case inr assump_12 =>
          apply False.elim assump_12
    case inr assump_8 =>
      cases assump_8
      case intro assump_23 assump_24 =>
        cases assump_24
        case inl assump_27 =>
          apply Or.inl
          intro assump_33
          intro assump_34
          apply True.intro
        case inr assump_28 =>
          apply Or.inl
          intro assump_39
          intro assump_40
          apply True.intro


variable (p0 p1 p2 p4 p5 : Prop)
theorem file72_32324 : (((((p0 ∧ p5) ∧ (p4 ∧ p5)) ∨ ((True → False) → (False → False))) ∨ (((p1 → p0) → False) ∧ ((p5 → False) → False))) ∨ ((((p2 → False) → (False → False)) → False) ∧ (((p5 → p5) ∨ (p4 → p1)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p2 p1 p6 p4 p0 : Prop)
theorem file72_32693 : (((((p0 ∧ p6) ∨ (True ∨ p2)) → False) → False) ∨ ((((p0 ∨ p1) ∧ (False ∧ False)) → False) ∨ (((True → p4) → (p4 ∨ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p0 ∧ p6) ∨ (True ∨ p2)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p5 p0 p3 p7 p4 p1 : Prop)
theorem file72_33093 : ((((((p0 → False) ∧ (p1 ∧ p0)) → False) → (((p4 ∨ p2) → (p5 → False)) → ((True ∧ True) ∧ (p3 → False)))) ∧ ((((p4 → False) → False) → ((p5 ∨ p7) ∨ (p4 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p4 → False) → False) → ((p5 ∨ p7) ∨ (p4 → p4))) := by
      intro assump_9
      apply Or.inr
      intro assump_12
      exact assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p5 p0 p2 p4 p7 p1 p6 p3 : Prop)
theorem file72_33642 : (((((False → False) ∨ (p4 → False)) ∧ ((p3 → p1) ∨ (p2 → p7))) ∧ (((True → False) ∨ (p7 → p3)) → ((p0 → p0) → False))) → ((((p2 ∧ p5) ∧ (p2 → False)) → ((p0 ∨ True) ∧ (p0 ∨ p3))) ∨ (((True ∨ p6) → (True ∨ p1)) ∧ ((p1 ∨ p4) ∧ (True ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          apply Or.inl
          intro assump_16
          apply And.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              apply Or.inr
              apply True.intro
          cases assump_16
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              have assump_132 : p2 := by
                exact assump_29
              let assump_37 := assump_28 assump_132
              apply False.elim assump_37
        case inr assump_11 =>
          apply Or.inl
          intro assump_45
          apply And.intro
          cases assump_45
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              apply Or.inr
              apply True.intro
          cases assump_45
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              have assump_133 : p2 := by
                exact assump_58
              let assump_66 := assump_57 assump_133
              apply False.elim assump_66
      case inr assump_7 =>
        cases assump_5
        case inl assump_72 =>
          apply Or.inl
          intro assump_78
          apply And.intro
          cases assump_78
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              apply Or.inr
              apply True.intro
          cases assump_78
          case intro assump_89 assump_90 =>
            cases assump_89
            case intro assump_91 assump_92 =>
              have assump_134 : p2 := by
                exact assump_91
              let assump_99 := assump_90 assump_134
              apply False.elim assump_99
        case inr assump_73 =>
          apply Or.inl
          intro assump_107
          apply And.intro
          cases assump_107
          case intro assump_108 assump_109 =>
            cases assump_108
            case intro assump_110 assump_111 =>
              apply Or.inr
              apply True.intro
          cases assump_107
          case intro assump_118 assump_119 =>
            cases assump_118
            case intro assump_120 assump_121 =>
              have assump_135 : p2 := by
                exact assump_120
              let assump_128 := assump_119 assump_135
              apply False.elim assump_128


variable (p0 p4 p6 p7 : Prop)
theorem file72_36674 : ((((((p7 → False) ∨ (False ∨ p6)) ∧ ((True ∧ False) ∧ (p4 → p0))) → False) → False) → False) := by
  intro assump_42
  have assump_78 : ((((p7 → False) ∨ (False ∨ p6)) ∧ ((True ∧ False) ∧ (p4 → p0))) → False) := by
    intro assump_46
    cases assump_46
    case intro assump_47 assump_48 =>
      cases assump_47
      case inl assump_49 =>
        cases assump_48
        case intro assump_53 assump_54 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            apply False.elim assump_56
      case inr assump_50 =>
        cases assump_50
        case inl assump_61 =>
          apply False.elim assump_61
        case inr assump_62 =>
          cases assump_48
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              apply False.elim assump_70
  let assump_45 := assump_42 assump_78
  apply False.elim assump_45


variable (p5 p7 p2 p6 p4 p0 p3 p1 : Prop)
theorem file72_37660 : ((((((p4 → False) → (p3 → False)) → False) ∧ (((p0 ∧ p1) ∨ (p4 → p2)) ∨ ((p0 → False) → False))) ∧ ((((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            have assump_60 : (((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) := by
              apply Or.inr
              apply Or.inl
              apply Or.inl
              exact assump_16
            let assump_24 := assump_7 assump_60
            apply False.elim assump_24
        case inr assump_15 =>
          have assump_61 : (((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) := by
            apply Or.inr
            apply Or.inr
            intro assump_33
            have assump_62 : (((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) := by
              apply Or.inr
              apply Or.inl
              apply Or.inr
              exact assump_33
            let assump_37 := assump_7 assump_62
            apply False.elim assump_37
          let assump_32 := assump_7 assump_61
          apply False.elim assump_32
      case inr assump_13 =>
        have assump_63 : (((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_49
          have assump_64 : (((p7 ∧ p6) ∧ (p0 ∨ p5)) ∨ ((p0 ∨ p3) ∨ (p3 → False))) := by
            apply Or.inr
            apply Or.inl
            apply Or.inr
            exact assump_49
          let assump_53 := assump_7 assump_64
          apply False.elim assump_53
        let assump_48 := assump_7 assump_63
        apply False.elim assump_48


variable (p1 p5 p2 p6 p3 p4 p0 p7 : Prop)
theorem file72_39596 : (((((p1 → True) → False) ∧ ((p0 ∧ p1) ∧ (p5 ∨ p6))) → False) ∨ ((((p3 ∨ p0) ∧ (p1 ∧ p4)) ∨ ((p5 → False) ∧ (p7 → p3))) ∨ (((p3 → p2) ∧ (p4 → p4)) ∨ ((p3 ∨ True) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          have assump_36 : (p1 → True) := by
            intro assump_22
            apply True.intro
          let assump_21 := assump_2 assump_36
          apply False.elim assump_21
        case inr assump_15 =>
          have assump_37 : (p1 → True) := by
            intro assump_32
            apply True.intro
          let assump_31 := assump_2 assump_37
          apply False.elim assump_31


variable (p2 p6 p1 p7 p3 p5 : Prop)
theorem file72_40485 : ((((((p5 ∨ p6) ∧ (False ∧ p2)) ∧ ((True ∧ p2) → False)) → (((False → False) ∨ (p3 → False)) ∧ ((p5 → p1) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_51 : ((((p5 ∨ p6) ∧ (False ∧ p2)) ∧ ((True ∧ p2) → False)) → (((False → False) ∨ (p3 → False)) ∧ ((p5 → p1) → (p7 → False)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
        case inr assump_11 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
    intro assump_24
    intro assump_25
    cases assump_5
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          cases assump_33
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
        case inr assump_35 =>
          cases assump_33
          case intro assump_44 assump_45 =>
            apply False.elim assump_44
  let assump_4 := assump_1 assump_51
  apply False.elim assump_4


variable (p3 p1 p2 p5 p7 : Prop)
theorem file72_41830 : (((((True ∨ p7) ∨ (False → False)) → False) ∧ (((p7 ∨ p2) → False) ∨ ((p3 ∨ p5) → False))) → ((((p1 → False) → False) → False) → False)) := by
  intro assump_10
  intro assump_11
  cases assump_10
  case intro assump_14 assump_15 =>
    cases assump_15
    case inl assump_18 =>
      have assump_34 : ((True ∨ p7) ∨ (False → False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_23 := assump_14 assump_34
      apply False.elim assump_23
    case inr assump_19 =>
      have assump_35 : ((True ∨ p7) ∨ (False → False)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_30 := assump_14 assump_35
      apply False.elim assump_30


variable (p1 p3 p4 p7 p5 p6 p2 : Prop)
theorem file72_42606 : ((((((True ∧ p1) → (p2 → p6)) ∨ ((p1 ∧ p7) ∧ (p3 → True))) → (((p7 → p4) ∧ (p4 → False)) → ((False → p3) ∧ (p5 → p5)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True ∧ p1) → (p2 → p6)) ∨ ((p1 ∧ p7) ∧ (p3 → True))) → (((p7 → p4) ∧ (p4 → False)) → ((False → p3) ∧ (p5 → p5)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    apply False.elim assump_7
    intro assump_10
    cases assump_6
    case intro assump_13 assump_14 =>
      cases assump_5
      case inl assump_19 =>
        exact assump_10
      case inr assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            exact assump_10
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p3 p4 p2 p5 p6 p1 p7 : Prop)
theorem file72_43487 : (((((True ∧ p1) → (p5 ∧ False)) → False) ∨ (((p4 ∧ p2) → False) ∨ ((p7 → False) ∧ (p4 ∧ p3)))) → ((((True → p6) ∧ (False ∧ p4)) ∧ ((p5 → p1) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p2 p3 p6 p1 p4 p0 p5 : Prop)
theorem file72_43951 : (((((False ∨ p6) ∨ (False → p6)) → False) → False) ∨ ((((p1 ∧ p4) ∧ (p3 → True)) → False) ∧ (((p6 ∧ p2) → False) → ((p5 → p0) ∨ (False ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False ∨ p6) ∨ (False → p6)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p7 p6 p5 p0 p2 : Prop)
theorem file72_44380 : (((((False → p5) ∧ (p2 ∧ False)) → False) ∨ (((p0 ∧ False) ∨ (p5 → False)) → ((p0 → False) ∧ (p0 → False)))) ∨ ((((p0 → False) → False) ∧ ((p7 → False) ∨ (False ∧ p4))) → (((p7 ∨ True) ∧ (p5 ∧ p0)) ∧ ((p6 → p2) ∧ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p4 p2 p1 p3 p0 p5 p6 p7 : Prop)
theorem file72_44867 : (((((p2 → p4) → False) → ((True → p4) ∨ (p3 ∨ p0))) → (((p6 ∧ p3) → False) → False)) → ((((True ∧ False) ∨ (True ∨ p5)) ∨ ((p0 ∧ p5) ∨ (p7 ∧ p4))) ∨ (((p5 → False) ∧ (p6 → False)) → ((p4 ∧ p1) ∨ (p5 ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p4 p3 p7 p2 p0 p1 p6 : Prop)
theorem file72_45241 : (((((p2 ∨ p0) → False) ∧ ((p3 → False) ∨ (p1 → False))) → (((p0 ∧ True) → False) → ((p4 ∨ p0) ∨ (p0 → p1)))) ∨ ((((p3 ∧ False) ∧ (p1 → False)) ∧ ((p7 → False) → False)) ∨ (((p4 → False) ∨ (True ∨ p6)) → ((p0 ∨ True) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      apply Or.inr
      intro assump_13
      have assump_33 : (p2 ∨ p0) := by
        apply Or.inr
        exact assump_13
      let assump_18 := assump_5 assump_33
      apply False.elim assump_18
    case inr assump_10 =>
      apply Or.inr
      intro assump_24
      have assump_34 : (p2 ∨ p0) := by
        apply Or.inr
        exact assump_24
      let assump_29 := assump_5 assump_34
      apply False.elim assump_29


variable (p6 p7 p1 p0 p2 p3 p5 : Prop)
theorem file72_46115 : (((((True → p6) ∧ (True → p2)) → False) → (((p6 ∧ p1) → (p5 ∨ True)) ∨ ((p6 → False) ∨ (p2 ∧ p7)))) ∨ ((((p2 → p5) ∧ (p1 → False)) ∨ ((p6 ∧ p3) → (p0 → False))) ∨ (((False → p1) → (p2 ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    apply True.intro


variable (p7 p0 p1 p3 p6 p4 : Prop)
theorem file72_46536 : (((((p7 → p4) ∨ (p4 → p7)) ∧ ((p6 ∨ p0) → False)) → (((p4 → False) → (p6 → p7)) ∧ ((p4 ∧ p0) → False))) ∨ ((((p3 → p1) ∧ (p4 → p3)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      have assump_55 : (p6 ∨ p0) := by
        apply Or.inl
        exact assump_3
      let assump_16 := assump_9 assump_55
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_56 : (p6 ∨ p0) := by
        apply Or.inl
        exact assump_3
      let assump_24 := assump_9 assump_56
      apply False.elim assump_24
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_1
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        have assump_57 : (p6 ∨ p0) := by
          apply Or.inr
          exact assump_30
        let assump_43 := assump_36 assump_57
        apply False.elim assump_43
      case inr assump_38 =>
        have assump_58 : (p6 ∨ p0) := by
          apply Or.inr
          exact assump_30
        let assump_51 := assump_36 assump_58
        apply False.elim assump_51


variable (p3 p2 p6 p0 p7 p1 p5 p4 : Prop)
theorem file72_47828 : (((((p2 ∧ p4) ∨ (p6 → False)) ∨ ((p3 ∧ False) ∨ (p7 → False))) → (((p2 → False) ∨ (p7 ∨ p4)) ∨ ((p4 ∧ p5) → False))) → ((((p4 → p1) ∨ (p1 → False)) → ((True → False) → (p3 ∨ p3))) ∨ (((False ∧ p0) → False) ∧ ((p1 ∧ p6) ∨ (p4 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_24 : True := by
      apply True.intro
    let assump_13 := assump_5 assump_24
    apply False.elim assump_13
  case inr assump_9 =>
    have assump_25 : True := by
      apply True.intro
    let assump_20 := assump_5 assump_25
    apply False.elim assump_20


variable (p3 p6 p2 p4 p7 p0 p1 : Prop)
theorem file72_48513 : (((((p0 ∧ p7) ∧ (p2 → p1)) → False) → (((p6 → p6) ∨ (p1 ∧ p2)) → ((p4 → False) → False))) → ((((p4 → False) ∧ (p0 ∨ True)) → ((p3 ∧ p2) → (p0 ∧ p2))) → (((p4 → p0) ∧ (False ∧ p0)) → ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      apply False.elim assump_11


variable (p7 p3 p2 p0 p1 p5 p6 p4 : Prop)
theorem file72_49002 : (((((p5 → True) ∨ (p2 → p7)) ∨ ((p6 ∧ p1) → (p6 → False))) ∨ (((p3 → p5) → (p6 → False)) → ((p1 → False) → (True ∧ p6)))) ∨ ((((p2 → False) → (p6 ∧ p2)) → False) ∧ (((p4 → p7) ∨ (p3 → p0)) ∨ ((p1 → False) ∧ (p3 ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply True.intro


variable (p7 p1 p0 p5 p6 : Prop)
theorem file72_49384 : ((((((p7 ∨ p1) → (False → p0)) ∨ ((p7 ∨ True) → False)) ∧ (((p6 ∨ p5) ∧ (False ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p7 ∨ p1) → (False → p0)) ∨ ((p7 ∨ True) → False)) ∧ (((p6 ∨ p5) ∧ (False ∧ p7)) → False)) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    cases assump_9
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
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p4 p3 p2 p7 p5 p6 : Prop)
theorem file72_50230 : (((((p4 → p7) ∧ (p2 ∨ p7)) ∨ ((p6 → p5) ∨ (False ∧ p6))) → (((p4 ∨ p3) ∧ (p7 ∨ p2)) → ((False → p4) → (False → p3)))) ∨ ((((p2 ∧ False) → (True → False)) → False) ∧ (((p5 ∨ p6) → (p4 ∨ p4)) ∨ ((p3 ∧ False) ∧ (True → False))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p6 p1 p4 p3 p5 p0 p7 : Prop)
theorem file72_50637 : ((((((False → False) ∨ (False → p1)) ∨ ((p1 ∧ p1) → (p0 ∨ p7))) ∨ (((p4 → p6) → (p3 ∨ p1)) ∨ ((p1 ∧ p5) → (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (False → p1)) ∨ ((p1 ∧ p1) → (p0 ∨ p7))) ∨ (((p4 → p6) → (p3 ∨ p1)) ∨ ((p1 ∧ p5) → (True ∧ True)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p2 p7 p0 p5 : Prop)
theorem file72_51169 : ((((((p2 → False) → False) ∨ ((p5 → p7) ∨ (p5 → False))) → False) ∧ ((((p7 → False) ∨ (p2 ∨ p0)) → ((False ∨ p7) → (p7 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p7 → False) ∨ (p2 ∨ p0)) → ((False ∨ p7) → (p7 ∨ p6))) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        cases assump_9
        case inl assump_17 =>
          apply Or.inl
          exact assump_12
        case inr assump_18 =>
          cases assump_18
          case inl assump_21 =>
            apply Or.inl
            exact assump_12
          case inr assump_22 =>
            apply Or.inl
            exact assump_12
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p2 p6 p3 p7 p1 p0 p4 p5 : Prop)
theorem file72_52093 : ((((((True ∨ False) ∧ (p2 → False)) → ((p4 ∧ p4) ∨ (p6 ∨ p7))) → (((p4 ∨ p7) ∧ (p6 → p5)) ∨ ((p2 → p3) → False))) ∧ ((((p5 → False) ∨ (False ∧ False)) ∧ ((p5 → False) → (p1 ∧ p7))) ∧ (((p6 → p1) → (p3 → False)) ∧ ((p0 ∧ p6) ∧ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_38 : p0 := by
                  exact assump_22
                let assump_30 := assump_21 assump_38
                apply False.elim assump_30
        case inr assump_11 =>
          cases assump_11
          case intro assump_34 assump_35 =>
            apply False.elim assump_34


variable (p0 p3 p1 p5 p7 : Prop)
theorem file72_53175 : ((((((p1 → False) → False) ∧ ((p3 ∨ True) → False)) → (((p7 → True) ∨ (p3 ∧ True)) ∧ ((p7 ∨ p0) ∧ (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 → False) → False) ∧ ((p3 ∨ True) → False)) → (((p7 → True) ∨ (p3 ∧ True)) ∧ ((p7 ∨ p0) ∧ (False → p5)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      apply True.intro
    apply And.intro
    cases assump_5
    case intro assump_13 assump_14 =>
      have assump_30 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_19 := assump_14 assump_30
      apply False.elim assump_19
    intro assump_23
    apply False.elim assump_23
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p6 p7 p0 p1 p3 p4 p5 p2 : Prop)
theorem file72_54047 : (((((p6 ∧ p2) → False) ∧ ((p2 → p5) ∨ (p4 → p6))) ∨ (((p1 ∧ p4) ∨ (p3 ∧ True)) → False)) → ((((True → False) → (p0 → p7)) ∨ ((p2 → p3) → (p4 ∨ p7))) ∨ (((p0 → False) ∨ (p3 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        intro assump_13
        have assump_46 : True := by
          apply True.intro
        let assump_18 := assump_12 assump_46
        apply False.elim assump_18
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_24
        intro assump_25
        have assump_47 : True := by
          apply True.intro
        let assump_30 := assump_24 assump_47
        apply False.elim assump_30
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_36
    intro assump_37
    have assump_48 : True := by
      apply True.intro
    let assump_42 := assump_36 assump_48
    apply False.elim assump_42


variable (p0 p4 p6 p7 p5 p3 p2 : Prop)
theorem file72_55186 : (((((p6 ∧ p2) ∨ (False ∧ p4)) → ((p2 → p6) ∨ (p0 ∧ p5))) → False) → ((((False ∧ p3) → (False → p4)) ∧ ((p7 ∧ p3) → (True → p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_31 : (((p6 ∧ p2) ∨ (False ∧ p4)) → ((p2 → p6) ∨ (p0 ∧ p5))) := by
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_21
          exact assump_15
      case inr assump_14 =>
        cases assump_14
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
    let assump_11 := assump_1 assump_31
    apply False.elim assump_11


variable (p3 p5 p0 p1 p4 : Prop)
theorem file72_55970 : (((((False ∨ p0) ∧ (True → False)) → False) → False) → ((((p1 ∨ p4) ∧ (p3 ∧ p5)) ∨ ((p5 → False) ∨ (p5 ∨ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          have assump_140 : (((False ∨ p0) ∧ (True → False)) → False) := by
            intro assump_20
            cases assump_20
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                apply False.elim assump_23
              case inr assump_24 =>
                have assump_141 : True := by
                  apply True.intro
                let assump_31 := assump_22 assump_141
                apply False.elim assump_31
          let assump_19 := assump_1 assump_140
          apply False.elim assump_19
      case inr assump_8 =>
        cases assump_6
        case intro assump_40 assump_41 =>
          have assump_142 : (((False ∨ p0) ∧ (True → False)) → False) := by
            intro assump_49
            cases assump_49
            case intro assump_50 assump_51 =>
              cases assump_50
              case inl assump_52 =>
                apply False.elim assump_52
              case inr assump_53 =>
                have assump_143 : True := by
                  apply True.intro
                let assump_60 := assump_51 assump_143
                apply False.elim assump_60
          let assump_48 := assump_1 assump_142
          apply False.elim assump_48
  case inr assump_4 =>
    cases assump_4
    case inl assump_67 =>
      have assump_144 : (((False ∨ p0) ∧ (True → False)) → False) := by
        intro assump_74
        cases assump_74
        case intro assump_75 assump_76 =>
          cases assump_75
          case inl assump_77 =>
            apply False.elim assump_77
          case inr assump_78 =>
            have assump_145 : True := by
              apply True.intro
            let assump_85 := assump_76 assump_145
            apply False.elim assump_85
      let assump_73 := assump_1 assump_144
      apply False.elim assump_73
    case inr assump_68 =>
      cases assump_68
      case inl assump_92 =>
        have assump_146 : (((False ∨ p0) ∧ (True → False)) → False) := by
          intro assump_99
          cases assump_99
          case intro assump_100 assump_101 =>
            cases assump_100
            case inl assump_102 =>
              apply False.elim assump_102
            case inr assump_103 =>
              have assump_147 : True := by
                apply True.intro
              let assump_110 := assump_101 assump_147
              apply False.elim assump_110
        let assump_98 := assump_1 assump_146
        apply False.elim assump_98
      case inr assump_93 =>
        have assump_148 : (((False ∨ p0) ∧ (True → False)) → False) := by
          intro assump_122
          cases assump_122
          case intro assump_123 assump_124 =>
            cases assump_123
            case inl assump_125 =>
              apply False.elim assump_125
            case inr assump_126 =>
              have assump_149 : True := by
                apply True.intro
              let assump_133 := assump_124 assump_149
              apply False.elim assump_133
        let assump_121 := assump_1 assump_148
        apply False.elim assump_121


variable (p6 p4 p7 p3 p0 p1 p2 p5 : Prop)
theorem file72_59499 : (((((p2 → False) ∨ (p4 → False)) ∨ ((p5 → False) ∧ (p4 ∨ p3))) → (((p4 ∨ p5) → (p1 ∨ p4)) ∧ ((p5 ∨ p6) → False))) → ((((p1 ∧ p5) → False) ∧ ((False ∧ p1) ∧ (p7 → False))) → (((True → p0) ∧ (p4 → False)) ∨ ((p4 ∨ p3) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p3 p1 : Prop)
theorem file72_60015 : ((((((p1 ∧ False) → (p3 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p1 ∧ False) → (p3 → False)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p1 ∧ False) → (p3 → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p3 p6 p2 p4 p1 : Prop)
theorem file72_60592 : (((((p6 ∨ p4) → (True ∨ False)) ∨ ((True → p5) → False)) ∧ (((False → False) → False) → False)) ∨ ((((False → p2) → (p1 ∨ p6)) → ((True → p2) → (p6 → False))) ∧ (((p1 → False) → (p3 ∨ False)) → False))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply True.intro
  intro assump_8
  have assump_18 : (False → False) := by
    intro assump_12
    apply False.elim assump_12
  let assump_11 := assump_8 assump_18
  apply False.elim assump_11


variable (p3 p5 p6 p2 p1 p0 p4 : Prop)
theorem file72_61244 : (((((False → False) → False) ∨ ((False → False) → (p6 ∨ p0))) ∨ (((p1 → False) ∧ (False → False)) ∨ ((p5 → False) ∧ (p5 ∧ p6)))) → ((((False → False) → False) → ((p0 ∨ p2) → False)) ∨ (((p2 → p4) → False) ∧ ((p3 ∧ p5) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        have assump_132 : (False → False) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_8 assump_132
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_133 : (False → False) := by
          intro assump_28
          apply False.elim assump_28
        let assump_27 := assump_8 assump_133
        apply False.elim assump_27
    case inr assump_5 =>
      apply Or.inl
      intro assump_36
      intro assump_37
      cases assump_37
      case inl assump_38 =>
        have assump_134 : (False → False) := by
          intro assump_45
          apply False.elim assump_45
        let assump_44 := assump_36 assump_134
        apply False.elim assump_44
      case inr assump_39 =>
        have assump_135 : (False → False) := by
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_36 assump_135
        apply False.elim assump_55
  case inr assump_3 =>
    cases assump_3
    case inl assump_62 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        apply Or.inl
        intro assump_70
        intro assump_71
        cases assump_71
        case inl assump_72 =>
          have assump_136 : (False → False) := by
            intro assump_79
            apply False.elim assump_79
          let assump_78 := assump_70 assump_136
          apply False.elim assump_78
        case inr assump_73 =>
          have assump_137 : (False → False) := by
            intro assump_90
            apply False.elim assump_90
          let assump_89 := assump_70 assump_137
          apply False.elim assump_89
    case inr assump_63 =>
      cases assump_63
      case intro assump_96 assump_97 =>
        cases assump_97
        case intro assump_100 assump_101 =>
          apply Or.inl
          intro assump_106
          intro assump_107
          cases assump_107
          case inl assump_108 =>
            have assump_138 : (False → False) := by
              intro assump_115
              apply False.elim assump_115
            let assump_114 := assump_106 assump_138
            apply False.elim assump_114
          case inr assump_109 =>
            have assump_139 : (False → False) := by
              intro assump_126
              apply False.elim assump_126
            let assump_125 := assump_106 assump_139
            apply False.elim assump_125


variable (p6 p3 : Prop)
theorem file72_64146 : ((((((False ∧ p3) → (True ∨ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p3) → (True ∨ p6)) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p3) → (True ∨ p6)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p1 p2 p5 p4 : Prop)
theorem file72_64695 : (((((True → p3) → (p5 → p5)) ∨ ((p3 → p1) ∧ (p2 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_14 : (((True → p3) → (p5 → p5)) ∨ ((p3 → p1) ∧ (p2 ∨ p4))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p1 p6 p0 p3 p4 p7 : Prop)
theorem file72_65073 : (((((p2 ∨ p6) ∧ (p2 → False)) → False) → (((p1 ∧ False) → False) ∨ ((p4 → p0) ∨ (p2 → p2)))) ∨ ((((p0 ∧ p0) ∧ (p3 → False)) ∨ ((False → False) ∧ (p1 → p1))) ∧ (((p7 → False) ∧ (p1 ∨ False)) → ((p3 ∨ p1) → False)))) := by
  apply Or.inl
  intro assump_40
  apply Or.inl
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    apply False.elim assump_45


variable (p5 p4 p0 p3 p6 p2 p1 : Prop)
theorem file72_65508 : (((((p6 → p6) → False) → ((p3 ∧ p2) → False)) ∨ (((p6 ∨ False) ∧ (True ∨ p0)) → ((p2 → False) ∧ (p0 ∨ p4)))) ∨ ((((p1 ∧ p6) → (p5 → p6)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : (p6 → p6) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_1 assump_18
    apply False.elim assump_11


variable (p7 p5 p0 p1 p3 p4 : Prop)
theorem file72_65997 : ((((((False ∨ False) → (False → False)) ∧ ((p7 ∧ p3) ∨ (p4 → p4))) ∨ (((p4 → p3) → (False → False)) ∧ ((p3 ∧ p5) ∨ (p1 → p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∨ False) → (False → False)) ∧ ((p7 ∧ p3) ∨ (p4 → p4))) ∨ (((p4 → p3) → (False → False)) ∧ ((p3 ∧ p5) ∨ (p1 → p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    apply Or.inr
    intro assump_9
    exact assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p1 p4 p5 p6 p0 p2 p3 : Prop)
theorem file72_66608 : (((((p5 ∧ p5) → False) → ((p5 ∧ p2) → False)) ∨ (((p4 → False) → (False ∨ p6)) → ((p3 → p3) → False))) ∨ ((((p4 ∧ p6) → False) ∧ ((p0 ∧ p7) → (p1 → p0))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_15 : (p5 ∧ p5) := by
      apply And.intro
      exact assump_3
      exact assump_3
    let assump_11 := assump_1 assump_15
    apply False.elim assump_11


variable (p7 p6 p1 p2 p0 p4 p5 : Prop)
theorem file72_67128 : ((((((p4 → True) ∨ (p5 ∨ p5)) ∨ ((p4 ∨ True) ∧ (p0 → p0))) ∨ (((p1 ∧ p6) ∧ (False → p7)) → False)) ∧ ((((p2 → False) → False) ∧ ((True → p0) → False)) ∧ (((p7 ∧ False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              have assump_158 : ((p7 ∧ False) → False) := by
                intro assump_23
                cases assump_23
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25
              let assump_22 := assump_13 assump_158
              apply False.elim assump_22
        case inr assump_9 =>
          cases assump_9
          case inl assump_33 =>
            cases assump_3
            case intro assump_37 assump_38 =>
              cases assump_37
              case intro assump_39 assump_40 =>
                have assump_159 : ((p7 ∧ False) → False) := by
                  intro assump_48
                  cases assump_48
                  case intro assump_49 assump_50 =>
                    apply False.elim assump_50
                let assump_47 := assump_38 assump_159
                apply False.elim assump_47
          case inr assump_34 =>
            cases assump_3
            case intro assump_60 assump_61 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                have assump_160 : ((p7 ∧ False) → False) := by
                  intro assump_71
                  cases assump_71
                  case intro assump_72 assump_73 =>
                    apply False.elim assump_73
                let assump_70 := assump_61 assump_160
                apply False.elim assump_70
      case inr assump_7 =>
        cases assump_7
        case intro assump_81 assump_82 =>
          cases assump_81
          case inl assump_83 =>
            cases assump_3
            case intro assump_89 assump_90 =>
              cases assump_89
              case intro assump_91 assump_92 =>
                have assump_161 : ((p7 ∧ False) → False) := by
                  intro assump_100
                  cases assump_100
                  case intro assump_101 assump_102 =>
                    apply False.elim assump_102
                let assump_99 := assump_90 assump_161
                apply False.elim assump_99
          case inr assump_84 =>
            cases assump_3
            case intro assump_114 assump_115 =>
              cases assump_114
              case intro assump_116 assump_117 =>
                have assump_162 : ((p7 ∧ False) → False) := by
                  intro assump_125
                  cases assump_125
                  case intro assump_126 assump_127 =>
                    apply False.elim assump_127
                let assump_124 := assump_115 assump_162
                apply False.elim assump_124
    case inr assump_5 =>
      cases assump_3
      case intro assump_137 assump_138 =>
        cases assump_137
        case intro assump_139 assump_140 =>
          have assump_163 : ((p7 ∧ False) → False) := by
            intro assump_148
            cases assump_148
            case intro assump_149 assump_150 =>
              apply False.elim assump_150
          let assump_147 := assump_138 assump_163
          apply False.elim assump_147


variable (p4 p7 p5 p1 p2 p0 p6 : Prop)
theorem file72_70742 : ((((((False → p6) ∧ (p2 → True)) ∧ ((p7 → False) → (True ∨ True))) ∨ (((p7 ∧ True) ∨ (p7 ∨ p5)) ∧ ((p1 → p4) → (p5 ∨ p2)))) → ((((p0 → True) → False) → ((False ∧ True) ∨ (p5 ∧ p0))) → False)) → False) := by
  intro assump_1
  have assump_24 : ((((False → p6) ∧ (p2 → True)) ∧ ((p7 → False) → (True ∨ True))) ∨ (((p7 ∧ True) ∨ (p7 ∨ p5)) ∧ ((p1 → p4) → (p5 ∨ p2)))) := by
    apply Or.inl
    apply And.intro
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply True.intro
    intro assump_9
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_24
  have assump_25 : (((p0 → True) → False) → ((False ∧ True) ∨ (p5 ∧ p0))) := by
    intro assump_13
    have assump_26 : (p0 → True) := by
      intro assump_17
      apply True.intro
    let assump_16 := assump_13 assump_26
    apply False.elim assump_16
  let assump_12 := assump_4 assump_25
  apply False.elim assump_12


variable (p3 p7 p5 p0 p1 p6 : Prop)
theorem file72_71736 : (((((p3 → False) ∨ (p5 ∧ False)) ∨ ((p5 → True) → (p1 → True))) ∨ (((p1 ∨ p6) ∨ (p3 → True)) ∨ ((False → p7) ∧ (p0 ∨ p7)))) → ((((True → False) → (p5 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_152 : ((True → False) → (p5 → False)) := by
          intro assump_15
          intro assump_16
          have assump_153 : True := by
            apply True.intro
          let assump_21 := assump_15 assump_153
          apply False.elim assump_21
        let assump_14 := assump_2 assump_152
        apply False.elim assump_14
      case inr assump_10 =>
        cases assump_10
        case intro assump_28 assump_29 =>
          apply False.elim assump_29
    case inr assump_8 =>
      have assump_154 : ((True → False) → (p5 → False)) := by
        intro assump_40
        intro assump_41
        have assump_155 : True := by
          apply True.intro
        let assump_46 := assump_40 assump_155
        apply False.elim assump_46
      let assump_39 := assump_2 assump_154
      apply False.elim assump_39
  case inr assump_6 =>
    cases assump_6
    case inl assump_53 =>
      cases assump_53
      case inl assump_55 =>
        cases assump_55
        case inl assump_57 =>
          have assump_156 : ((True → False) → (p5 → False)) := by
            intro assump_63
            intro assump_64
            have assump_157 : True := by
              apply True.intro
            let assump_69 := assump_63 assump_157
            apply False.elim assump_69
          let assump_62 := assump_2 assump_156
          apply False.elim assump_62
        case inr assump_58 =>
          have assump_158 : ((True → False) → (p5 → False)) := by
            intro assump_80
            intro assump_81
            have assump_159 : True := by
              apply True.intro
            let assump_86 := assump_80 assump_159
            apply False.elim assump_86
          let assump_79 := assump_2 assump_158
          apply False.elim assump_79
      case inr assump_56 =>
        have assump_160 : ((True → False) → (p5 → False)) := by
          intro assump_97
          intro assump_98
          have assump_161 : True := by
            apply True.intro
          let assump_103 := assump_97 assump_161
          apply False.elim assump_103
        let assump_96 := assump_2 assump_160
        apply False.elim assump_96
    case inr assump_54 =>
      cases assump_54
      case intro assump_110 assump_111 =>
        cases assump_111
        case inl assump_114 =>
          have assump_162 : ((True → False) → (p5 → False)) := by
            intro assump_121
            intro assump_122
            have assump_163 : True := by
              apply True.intro
            let assump_127 := assump_121 assump_163
            apply False.elim assump_127
          let assump_120 := assump_2 assump_162
          apply False.elim assump_120
        case inr assump_115 =>
          have assump_164 : ((True → False) → (p5 → False)) := by
            intro assump_139
            intro assump_140
            have assump_165 : True := by
              apply True.intro
            let assump_145 := assump_139 assump_165
            apply False.elim assump_145
          let assump_138 := assump_2 assump_164
          apply False.elim assump_138


variable (p0 p5 p6 p4 p2 p7 p3 p1 : Prop)
theorem file72_75229 : (((((p4 ∧ p5) ∧ (p1 → False)) → False) → (((True → False) → (False → p0)) ∨ ((p3 ∨ p7) → (p2 ∨ False)))) ∨ ((((p4 ∨ p4) → False) → False) ∧ (((p6 → p3) ∧ (p1 ∨ p3)) ∧ ((p5 → False) → (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p2 p7 p0 p4 p6 p1 p3 p5 : Prop)
theorem file72_75610 : (((((p3 → False) ∧ (p5 → False)) ∧ ((p5 → p1) ∨ (False ∧ p2))) ∨ (((p7 ∨ p1) ∨ (p4 → p0)) ∧ ((p5 → p1) → (p2 → False)))) → ((((p3 → False) → (p5 ∧ False)) → ((True → False) → (p6 → False))) → (((p0 → p1) → (p6 ∨ p7)) → ((p3 → p3) ∨ (p4 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          apply Or.inl
          intro assump_22
          exact assump_22
        case inr assump_19 =>
          cases assump_19
          case intro assump_25 assump_26 =>
            apply False.elim assump_25
  case inr assump_9 =>
    cases assump_9
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        cases assump_31
        case inl assump_33 =>
          apply Or.inl
          intro assump_39
          exact assump_39
        case inr assump_34 =>
          apply Or.inl
          intro assump_46
          exact assump_46
      case inr assump_32 =>
        apply Or.inl
        intro assump_53
        exact assump_53


variable (p1 p6 p0 p3 p4 p7 : Prop)
theorem file72_76861 : (((((p3 ∨ True) → (p0 ∨ p0)) ∧ ((p0 → False) ∧ (p0 → False))) → False) ∨ ((((p7 ∧ p6) ∨ (p1 → False)) ∨ ((p0 → p1) ∧ (p1 ∧ p6))) ∧ (((p0 ∧ p4) ∧ (p4 ∨ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_32 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_14 := assump_2 assump_32
      cases assump_14
      case inl assump_16 =>
        have assump_33 : p0 := by
          exact assump_16
        let assump_21 := assump_7 assump_33
        apply False.elim assump_21
      case inr assump_17 =>
        have assump_34 : p0 := by
          exact assump_17
        let assump_28 := assump_7 assump_34
        apply False.elim assump_28


variable (p6 p0 p4 p5 p1 p3 p2 : Prop)
theorem file72_77720 : (((((False ∨ p3) → (p4 ∨ p3)) → False) → (((p3 → False) ∧ (p6 → p0)) ∨ ((p1 ∨ p2) ∨ (p3 ∨ p4)))) ∨ ((((p2 ∧ p2) → False) → False) → (((p2 → False) → (p5 → False)) → ((True ∧ p3) → (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_34 : ((False ∨ p3) → (p4 ∨ p3)) := by
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply Or.inr
      exact assump_11
  let assump_8 := assump_1 assump_34
  apply False.elim assump_8
  intro assump_19
  have assump_35 : ((False ∨ p3) → (p4 ∨ p3)) := by
    intro assump_24
    cases assump_24
    case inl assump_25 =>
      apply False.elim assump_25
    case inr assump_26 =>
      apply Or.inr
      exact assump_26
  let assump_23 := assump_1 assump_35
  apply False.elim assump_23


variable (p2 p3 p5 : Prop)
theorem file72_78640 : (((((p2 ∨ p5) → False) → ((False → False) → False)) ∧ (((True ∧ False) → (p3 ∧ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True ∧ False) → (p3 ∧ True)) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
      apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p0 p5 p7 p1 p3 p6 : Prop)
theorem file72_79171 : (((((p1 → p7) → (p5 ∨ p0)) → ((p7 → p6) → (p5 → p3))) → (((False → p6) ∨ (False ∧ p0)) ∨ ((p6 → p4) ∧ (p5 ∨ p4)))) ∧ ((((p6 ∧ p7) ∧ (True ∨ p4)) ∧ ((False → False) → False)) → False)) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          have assump_42 : (False → False) := by
            intro assump_25
            apply False.elim assump_25
          let assump_24 := assump_9 assump_42
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_43 : (False → False) := by
            intro assump_36
            apply False.elim assump_36
          let assump_35 := assump_9 assump_43
          apply False.elim assump_35


variable (p5 p1 p6 p7 p0 : Prop)
theorem file72_80197 : ((((((False → p6) ∨ (p5 → False)) → False) → (((p0 → False) → False) → ((p7 ∨ p1) ∨ (p0 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((False → p6) ∨ (p5 → False)) → False) → (((p0 → False) → False) → ((p7 ∨ p1) ∨ (p0 ∧ True)))) := by
    intro assump_5
    intro assump_6
    have assump_22 : ((False → p6) ∨ (p5 → False)) := by
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p2 p4 p0 p3 p5 p1 p6 : Prop)
theorem file72_80830 : (((((p3 → p0) ∨ (p0 → p1)) ∨ ((p3 → False) ∧ (p4 → False))) ∨ (((p0 → False) ∨ (True → p7)) ∨ ((False → p2) → False))) → ((((p7 ∧ p2) → (p7 ∨ p0)) → False) → (((p4 ∨ p6) ∧ (True → False)) → ((p5 ∧ p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_1
        case inl assump_21 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_23
            case inl assump_25 =>
              have assump_199 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_31
                cases assump_31
                case intro assump_32 assump_33 =>
                  apply Or.inl
                  exact assump_32
              let assump_30 := assump_2 assump_199
              apply False.elim assump_30
            case inr assump_26 =>
              have assump_200 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_45
                cases assump_45
                case intro assump_46 assump_47 =>
                  apply Or.inl
                  exact assump_46
              let assump_44 := assump_2 assump_200
              apply False.elim assump_44
          case inr assump_24 =>
            cases assump_24
            case intro assump_55 assump_56 =>
              have assump_201 : p4 := by
                exact assump_13
              let assump_61 := assump_56 assump_201
              apply False.elim assump_61
        case inr assump_22 =>
          cases assump_22
          case inl assump_65 =>
            cases assump_65
            case inl assump_67 =>
              have assump_202 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_73
                cases assump_73
                case intro assump_74 assump_75 =>
                  apply Or.inl
                  exact assump_74
              let assump_72 := assump_2 assump_202
              apply False.elim assump_72
            case inr assump_68 =>
              have assump_203 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_88
                cases assump_88
                case intro assump_89 assump_90 =>
                  apply Or.inl
                  exact assump_89
              let assump_87 := assump_2 assump_203
              apply False.elim assump_87
          case inr assump_66 =>
            have assump_204 : (False → p2) := by
              intro assump_101
              apply False.elim assump_101
            let assump_100 := assump_66 assump_204
            apply False.elim assump_100
      case inr assump_14 =>
        cases assump_1
        case inl assump_113 =>
          cases assump_113
          case inl assump_115 =>
            cases assump_115
            case inl assump_117 =>
              have assump_205 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_123
                cases assump_123
                case intro assump_124 assump_125 =>
                  apply Or.inl
                  exact assump_124
              let assump_122 := assump_2 assump_205
              apply False.elim assump_122
            case inr assump_118 =>
              have assump_206 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_137
                cases assump_137
                case intro assump_138 assump_139 =>
                  apply Or.inl
                  exact assump_138
              let assump_136 := assump_2 assump_206
              apply False.elim assump_136
          case inr assump_116 =>
            cases assump_116
            case intro assump_147 assump_148 =>
              have assump_207 : p4 := by
                exact assump_6
              let assump_153 := assump_148 assump_207
              apply False.elim assump_153
        case inr assump_114 =>
          cases assump_114
          case inl assump_157 =>
            cases assump_157
            case inl assump_159 =>
              have assump_208 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_165
                cases assump_165
                case intro assump_166 assump_167 =>
                  apply Or.inl
                  exact assump_166
              let assump_164 := assump_2 assump_208
              apply False.elim assump_164
            case inr assump_160 =>
              have assump_209 : ((p7 ∧ p2) → (p7 ∨ p0)) := by
                intro assump_180
                cases assump_180
                case intro assump_181 assump_182 =>
                  apply Or.inl
                  exact assump_181
              let assump_179 := assump_2 assump_209
              apply False.elim assump_179
          case inr assump_158 =>
            have assump_210 : (False → p2) := by
              intro assump_193
              apply False.elim assump_193
            let assump_192 := assump_158 assump_210
            apply False.elim assump_192


variable (p1 p3 p4 p5 p0 : Prop)
theorem file72_85888 : (((((p5 ∨ p4) → (False → p0)) ∧ ((p1 ∨ True) ∨ (p4 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p5 ∨ p4) → (False → p0)) ∧ ((p1 ∨ True) ∨ (p4 ∧ p3))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p3 p1 p2 p5 p7 p0 : Prop)
theorem file72_86338 : ((((((False → False) ∧ (p5 → True)) ∨ ((p2 ∨ p3) ∧ (True → False))) ∨ (((True ∨ p7) ∨ (p0 ∨ p1)) ∨ ((p7 → False) ∨ (p2 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((False → False) ∧ (p5 → True)) ∨ ((p2 ∨ p3) ∧ (True → False))) ∨ (((True ∨ p7) ∨ (p0 ∨ p1)) ∨ ((p7 → False) ∨ (p2 → True)))) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p0 p6 p7 p3 : Prop)
theorem file72_86927 : ((((((p3 ∧ p7) ∧ (p0 → p6)) ∨ ((p0 ∧ p2) → False)) → False) ∧ ((((p2 → p0) → (p2 → False)) → False) ∧ (((p0 ∨ p2) ∨ (p2 ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_30 : ((p2 → p0) → (p2 → False)) := by
        intro assump_14
        intro assump_15
        have assump_31 : ((p0 ∨ p2) ∨ (p2 ∧ p0)) := by
          apply Or.inl
          apply Or.inr
          exact assump_15
        let assump_23 := assump_7 assump_31
        apply False.elim assump_23
      let assump_13 := assump_6 assump_30
      apply False.elim assump_13


variable (p6 p7 p3 p4 p2 : Prop)
theorem file72_87645 : (((((True ∨ p4) ∨ (p3 ∨ p7)) ∧ ((False → p6) ∨ (p2 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_11 : (((True ∨ p4) ∨ (p3 ∨ p7)) ∧ ((False → p6) ∨ (p2 ∧ p6))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    apply True.intro
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p1 p7 p6 p5 p4 p3 : Prop)
theorem file72_88096 : (((((p7 ∧ p3) ∨ (p1 → False)) → False) ∧ (((True → False) ∧ (p5 ∧ p0)) ∧ ((p1 ∨ p7) ∧ (p7 → p4)))) → ((((p1 → False) ∧ (p1 ∨ p6)) ∨ ((p0 → p6) ∨ (p4 ∧ p7))) ∧ (((True → p6) ∨ (p6 ∧ True)) ∧ ((p3 ∧ p4) → (p4 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              apply And.intro
              intro assump_26
              have assump_174 : True := by
                apply True.intro
              let assump_34 := assump_8 assump_174
              apply False.elim assump_34
              apply Or.inl
              exact assump_20
            case inr assump_21 =>
              apply Or.inr
              apply Or.inl
              intro assump_55
              have assump_175 : True := by
                apply True.intro
              let assump_64 := assump_8 assump_175
              apply False.elim assump_64
  apply And.intro
  cases assump_1
  case intro assump_68 assump_69 =>
    cases assump_69
    case intro assump_72 assump_73 =>
      cases assump_72
      case intro assump_74 assump_75 =>
        cases assump_75
        case intro assump_78 assump_79 =>
          cases assump_73
          case intro assump_84 assump_85 =>
            cases assump_84
            case inl assump_86 =>
              apply Or.inl
              intro assump_92
              have assump_176 : True := by
                apply True.intro
              let assump_99 := assump_74 assump_176
              apply False.elim assump_99
            case inr assump_87 =>
              apply Or.inl
              intro assump_107
              have assump_177 : True := by
                apply True.intro
              let assump_115 := assump_74 assump_177
              apply False.elim assump_115
  intro assump_119
  intro assump_120
  cases assump_119
  case intro assump_123 assump_124 =>
    cases assump_1
    case intro assump_129 assump_130 =>
      cases assump_130
      case intro assump_133 assump_134 =>
        cases assump_133
        case intro assump_135 assump_136 =>
          cases assump_136
          case intro assump_139 assump_140 =>
            cases assump_134
            case intro assump_145 assump_146 =>
              cases assump_145
              case inl assump_147 =>
                have assump_178 : True := by
                  apply True.intro
                let assump_157 := assump_135 assump_178
                apply False.elim assump_157
              case inr assump_148 =>
                have assump_179 : True := by
                  apply True.intro
                let assump_170 := assump_135 assump_179
                apply False.elim assump_170


variable (p3 p0 p5 p6 p4 p1 p7 : Prop)
theorem file72_91160 : (((((p4 ∧ False) ∨ (True → False)) ∧ ((p0 ∨ p5) → (p3 → False))) → False) ∨ ((((p6 ∨ p7) → (p5 ∨ p0)) → ((p7 → p1) → False)) ∧ (((p6 → False) ∧ (p3 ∧ p0)) ∧ ((p4 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7
    case inr assump_5 =>
      have assump_21 : True := by
        apply True.intro
      let assump_17 := assump_5 assump_21
      apply False.elim assump_17


variable (p3 p1 p6 p5 p7 p4 : Prop)
theorem file72_91788 : (((((p6 → False) ∨ (p7 → False)) ∧ ((False → p7) → False)) ∧ (((True → False) ∨ (p3 ∨ p4)) ∨ ((p3 → p4) ∨ (p7 ∧ p6)))) → ((((True ∧ p7) → (True → p7)) ∧ ((p1 ∨ p6) → (p5 → False))) ∨ (((p3 ∨ False) → (True ∨ p6)) ∨ ((p6 → False) ∨ (p1 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            apply Or.inl
            apply And.intro
            intro assump_18
            intro assump_19
            cases assump_18
            case intro assump_22 assump_23 =>
              exact assump_23
            intro assump_28
            intro assump_29
            cases assump_28
            case inl assump_32 =>
              have assump_448 : True := by
                apply True.intro
              let assump_38 := assump_14 assump_448
              apply False.elim assump_38
            case inr assump_33 =>
              have assump_449 : True := by
                apply True.intro
              let assump_46 := assump_14 assump_449
              apply False.elim assump_46
          case inr assump_15 =>
            cases assump_15
            case inl assump_50 =>
              apply Or.inl
              apply And.intro
              intro assump_54
              intro assump_55
              cases assump_54
              case intro assump_58 assump_59 =>
                exact assump_59
              intro assump_64
              intro assump_65
              cases assump_64
              case inl assump_68 =>
                have assump_450 : (False → p7) := by
                  intro assump_76
                  apply False.elim assump_76
                let assump_75 := assump_5 assump_450
                apply False.elim assump_75
              case inr assump_69 =>
                have assump_451 : (False → p7) := by
                  intro assump_88
                  apply False.elim assump_88
                let assump_87 := assump_5 assump_451
                apply False.elim assump_87
            case inr assump_51 =>
              apply Or.inl
              apply And.intro
              intro assump_96
              intro assump_97
              cases assump_96
              case intro assump_100 assump_101 =>
                exact assump_101
              intro assump_106
              intro assump_107
              cases assump_106
              case inl assump_110 =>
                have assump_452 : (False → p7) := by
                  intro assump_118
                  apply False.elim assump_118
                let assump_117 := assump_5 assump_452
                apply False.elim assump_117
              case inr assump_111 =>
                have assump_453 : (False → p7) := by
                  intro assump_130
                  apply False.elim assump_130
                let assump_129 := assump_5 assump_453
                apply False.elim assump_129
        case inr assump_13 =>
          cases assump_13
          case inl assump_136 =>
            apply Or.inl
            apply And.intro
            intro assump_140
            intro assump_141
            cases assump_140
            case intro assump_144 assump_145 =>
              exact assump_145
            intro assump_150
            intro assump_151
            cases assump_150
            case inl assump_154 =>
              have assump_454 : (False → p7) := by
                intro assump_162
                apply False.elim assump_162
              let assump_161 := assump_5 assump_454
              apply False.elim assump_161
            case inr assump_155 =>
              have assump_455 : (False → p7) := by
                intro assump_174
                apply False.elim assump_174
              let assump_173 := assump_5 assump_455
              apply False.elim assump_173
          case inr assump_137 =>
            cases assump_137
            case intro assump_180 assump_181 =>
              apply Or.inl
              apply And.intro
              intro assump_186
              intro assump_187
              cases assump_186
              case intro assump_190 assump_191 =>
                exact assump_191
              intro assump_196
              intro assump_197
              cases assump_196
              case inl assump_200 =>
                have assump_456 : (False → p7) := by
                  intro assump_209
                  apply False.elim assump_209
                let assump_208 := assump_5 assump_456
                apply False.elim assump_208
              case inr assump_201 =>
                have assump_457 : (False → p7) := by
                  intro assump_222
                  apply False.elim assump_222
                let assump_221 := assump_5 assump_457
                apply False.elim assump_221
      case inr assump_7 =>
        cases assump_3
        case inl assump_232 =>
          cases assump_232
          case inl assump_234 =>
            apply Or.inl
            apply And.intro
            intro assump_238
            intro assump_239
            cases assump_238
            case intro assump_242 assump_243 =>
              exact assump_243
            intro assump_248
            intro assump_249
            cases assump_248
            case inl assump_252 =>
              have assump_458 : True := by
                apply True.intro
              let assump_258 := assump_234 assump_458
              apply False.elim assump_258
            case inr assump_253 =>
              have assump_459 : True := by
                apply True.intro
              let assump_266 := assump_234 assump_459
              apply False.elim assump_266
          case inr assump_235 =>
            cases assump_235
            case inl assump_270 =>
              apply Or.inl
              apply And.intro
              intro assump_274
              intro assump_275
              cases assump_274
              case intro assump_278 assump_279 =>
                exact assump_279
              intro assump_284
              intro assump_285
              cases assump_284
              case inl assump_288 =>
                have assump_460 : (False → p7) := by
                  intro assump_296
                  apply False.elim assump_296
                let assump_295 := assump_5 assump_460
                apply False.elim assump_295
              case inr assump_289 =>
                have assump_461 : (False → p7) := by
                  intro assump_308
                  apply False.elim assump_308
                let assump_307 := assump_5 assump_461
                apply False.elim assump_307
            case inr assump_271 =>
              apply Or.inl
              apply And.intro
              intro assump_316
              intro assump_317
              cases assump_316
              case intro assump_320 assump_321 =>
                exact assump_321
              intro assump_326
              intro assump_327
              cases assump_326
              case inl assump_330 =>
                have assump_462 : (False → p7) := by
                  intro assump_338
                  apply False.elim assump_338
                let assump_337 := assump_5 assump_462
                apply False.elim assump_337
              case inr assump_331 =>
                have assump_463 : (False → p7) := by
                  intro assump_350
                  apply False.elim assump_350
                let assump_349 := assump_5 assump_463
                apply False.elim assump_349
        case inr assump_233 =>
          cases assump_233
          case inl assump_356 =>
            apply Or.inl
            apply And.intro
            intro assump_360
            intro assump_361
            cases assump_360
            case intro assump_364 assump_365 =>
              exact assump_365
            intro assump_370
            intro assump_371
            cases assump_370
            case inl assump_374 =>
              have assump_464 : (False → p7) := by
                intro assump_382
                apply False.elim assump_382
              let assump_381 := assump_5 assump_464
              apply False.elim assump_381
            case inr assump_375 =>
              have assump_465 : (False → p7) := by
                intro assump_394
                apply False.elim assump_394
              let assump_393 := assump_5 assump_465
              apply False.elim assump_393
          case inr assump_357 =>
            cases assump_357
            case intro assump_400 assump_401 =>
              apply Or.inl
              apply And.intro
              intro assump_406
              intro assump_407
              cases assump_406
              case intro assump_410 assump_411 =>
                exact assump_411
              intro assump_416
              intro assump_417
              cases assump_416
              case inl assump_420 =>
                have assump_466 : (False → p7) := by
                  intro assump_429
                  apply False.elim assump_429
                let assump_428 := assump_5 assump_466
                apply False.elim assump_428
              case inr assump_421 =>
                have assump_467 : (False → p7) := by
                  intro assump_442
                  apply False.elim assump_442
                let assump_441 := assump_5 assump_467
                apply False.elim assump_441


variable (p0 p5 p3 p1 p2 p7 p6 p4 : Prop)
theorem file72_101415 : (((((p0 ∧ False) → (p5 → False)) ∧ ((p6 ∨ p6) → (p6 ∧ p4))) ∧ (((True ∨ p5) → False) ∧ ((True → p0) ∧ (p3 → False)))) → ((((p6 ∨ p5) ∧ (p4 ∨ p6)) ∨ ((p5 → False) ∨ (p2 ∧ p1))) ∧ (((p4 → False) → False) ∧ ((p0 ∨ p4) → (p7 → p5))))) := by
  intro assump_8
  apply And.intro
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_10
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply Or.inr
          apply Or.inl
          intro assump_27
          have assump_126 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_34 := assump_17 assump_126
          apply False.elim assump_34
  apply And.intro
  intro assump_38
  cases assump_8
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      cases assump_42
      case intro assump_49 assump_50 =>
        cases assump_50
        case intro assump_53 assump_54 =>
          have assump_127 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_62 := assump_49 assump_127
          apply False.elim assump_62
  intro assump_66
  intro assump_67
  cases assump_66
  case inl assump_70 =>
    cases assump_8
    case intro assump_74 assump_75 =>
      cases assump_74
      case intro assump_76 assump_77 =>
        cases assump_75
        case intro assump_82 assump_83 =>
          cases assump_83
          case intro assump_86 assump_87 =>
            have assump_128 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_95 := assump_82 assump_128
            apply False.elim assump_95
  case inr assump_71 =>
    cases assump_8
    case intro assump_101 assump_102 =>
      cases assump_101
      case intro assump_103 assump_104 =>
        cases assump_102
        case intro assump_109 assump_110 =>
          cases assump_110
          case intro assump_113 assump_114 =>
            have assump_129 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_122 := assump_109 assump_129
            apply False.elim assump_122


variable (p0 p4 p5 p1 p6 : Prop)
theorem file72_103714 : ((((((p5 → p1) ∨ (p4 → p4)) → ((p4 → p6) ∧ (p1 → False))) → False) ∧ ((((p0 → False) → False) → ((p6 → p1) → (True ∧ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : (((p0 → False) → False) → ((p6 → p1) → (True ∧ True))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_14
    apply False.elim assump_8


variable (p7 p1 p0 p3 p6 p5 p2 : Prop)
theorem file72_104257 : ((((((p3 ∧ p7) ∨ (p2 ∧ p1)) ∧ ((p0 → False) → (p7 → p5))) ∧ (((False → False) → (False ∧ p0)) ∧ ((True → False) ∨ (p0 → False)))) ∧ ((((p7 ∨ p3) → False) ∨ ((p6 → p0) → False)) ∧ (((p6 ∨ p1) ∧ (p6 → p0)) ∧ ((p7 → False) ∧ (False → False))))) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    cases assump_27
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        cases assump_34
                        case inl assump_36 =>
                          cases assump_33
                          case intro assump_42 assump_43 =>
                            have assump_440 : p7 := by
                              exact assump_11
                            let assump_49 := assump_42 assump_440
                            apply False.elim assump_49
                        case inr assump_37 =>
                          cases assump_33
                          case intro assump_57 assump_58 =>
                            have assump_441 : p7 := by
                              exact assump_11
                            let assump_64 := assump_57 assump_441
                            apply False.elim assump_64
                  case inr assump_29 =>
                    cases assump_27
                    case intro assump_70 assump_71 =>
                      cases assump_70
                      case intro assump_72 assump_73 =>
                        cases assump_72
                        case inl assump_74 =>
                          cases assump_71
                          case intro assump_80 assump_81 =>
                            have assump_442 : p7 := by
                              exact assump_11
                            let assump_87 := assump_80 assump_442
                            apply False.elim assump_87
                        case inr assump_75 =>
                          cases assump_71
                          case intro assump_95 assump_96 =>
                            have assump_443 : p7 := by
                              exact assump_11
                            let assump_102 := assump_95 assump_443
                            apply False.elim assump_102
              case inr assump_23 =>
                cases assump_3
                case intro assump_108 assump_109 =>
                  cases assump_108
                  case inl assump_110 =>
                    cases assump_109
                    case intro assump_114 assump_115 =>
                      cases assump_114
                      case intro assump_116 assump_117 =>
                        cases assump_116
                        case inl assump_118 =>
                          cases assump_115
                          case intro assump_124 assump_125 =>
                            have assump_444 : p7 := by
                              exact assump_11
                            let assump_131 := assump_124 assump_444
                            apply False.elim assump_131
                        case inr assump_119 =>
                          cases assump_115
                          case intro assump_139 assump_140 =>
                            have assump_445 : p7 := by
                              exact assump_11
                            let assump_146 := assump_139 assump_445
                            apply False.elim assump_146
                  case inr assump_111 =>
                    cases assump_109
                    case intro assump_152 assump_153 =>
                      cases assump_152
                      case intro assump_154 assump_155 =>
                        cases assump_154
                        case inl assump_156 =>
                          cases assump_153
                          case intro assump_162 assump_163 =>
                            have assump_446 : p7 := by
                              exact assump_11
                            let assump_169 := assump_162 assump_446
                            apply False.elim assump_169
                        case inr assump_157 =>
                          cases assump_153
                          case intro assump_177 assump_178 =>
                            have assump_447 : p7 := by
                              exact assump_11
                            let assump_184 := assump_177 assump_447
                            apply False.elim assump_184
        case inr assump_9 =>
          cases assump_9
          case intro assump_188 assump_189 =>
            cases assump_5
            case intro assump_196 assump_197 =>
              cases assump_197
              case inl assump_200 =>
                cases assump_3
                case intro assump_204 assump_205 =>
                  cases assump_204
                  case inl assump_206 =>
                    cases assump_205
                    case intro assump_210 assump_211 =>
                      cases assump_210
                      case intro assump_212 assump_213 =>
                        cases assump_212
                        case inl assump_214 =>
                          cases assump_211
                          case intro assump_220 assump_221 =>
                            have assump_448 : True := by
                              apply True.intro
                            let assump_232 := assump_200 assump_448
                            apply False.elim assump_232
                        case inr assump_215 =>
                          cases assump_211
                          case intro assump_240 assump_241 =>
                            have assump_449 : True := by
                              apply True.intro
                            let assump_251 := assump_200 assump_449
                            apply False.elim assump_251
                  case inr assump_207 =>
                    cases assump_205
                    case intro assump_257 assump_258 =>
                      cases assump_257
                      case intro assump_259 assump_260 =>
                        cases assump_259
                        case inl assump_261 =>
                          cases assump_258
                          case intro assump_267 assump_268 =>
                            have assump_450 : (p6 → p0) := by
                              intro assump_279
                              have assump_451 : p6 := by
                                exact assump_279
                              let assump_285 := assump_260 assump_451
                              exact assump_285
                            let assump_278 := assump_207 assump_450
                            apply False.elim assump_278
                        case inr assump_262 =>
                          cases assump_258
                          case intro assump_294 assump_295 =>
                            have assump_452 : (p6 → p0) := by
                              intro assump_305
                              have assump_453 : p6 := by
                                exact assump_305
                              let assump_311 := assump_260 assump_453
                              exact assump_311
                            let assump_304 := assump_207 assump_452
                            apply False.elim assump_304
              case inr assump_201 =>
                cases assump_3
                case intro assump_318 assump_319 =>
                  cases assump_318
                  case inl assump_320 =>
                    cases assump_319
                    case intro assump_324 assump_325 =>
                      cases assump_324
                      case intro assump_326 assump_327 =>
                        cases assump_326
                        case inl assump_328 =>
                          cases assump_325
                          case intro assump_334 assump_335 =>
                            have assump_454 : (False → False) := by
                              intro assump_348
                              apply False.elim assump_348
                            let assump_347 := assump_196 assump_454
                            let assump_351 := And.left assump_347
                            apply False.elim assump_351
                        case inr assump_329 =>
                          cases assump_325
                          case intro assump_359 assump_360 =>
                            have assump_455 : (False → False) := by
                              intro assump_372
                              apply False.elim assump_372
                            let assump_371 := assump_196 assump_455
                            let assump_375 := And.left assump_371
                            apply False.elim assump_375
                  case inr assump_321 =>
                    cases assump_319
                    case intro assump_381 assump_382 =>
                      cases assump_381
                      case intro assump_383 assump_384 =>
                        cases assump_383
                        case inl assump_385 =>
                          cases assump_382
                          case intro assump_391 assump_392 =>
                            have assump_456 : (p6 → p0) := by
                              intro assump_403
                              have assump_457 : p6 := by
                                exact assump_403
                              let assump_409 := assump_384 assump_457
                              exact assump_409
                            let assump_402 := assump_321 assump_456
                            apply False.elim assump_402
                        case inr assump_386 =>
                          cases assump_382
                          case intro assump_418 assump_419 =>
                            have assump_458 : (p6 → p0) := by
                              intro assump_429
                              have assump_459 : p6 := by
                                exact assump_429
                              let assump_435 := assump_384 assump_459
                              exact assump_435
                            let assump_428 := assump_321 assump_458
                            apply False.elim assump_428


variable (p5 p0 p2 p6 p4 p1 : Prop)
theorem file72_115173 : ((((((True ∨ p4) → (p6 → False)) ∧ ((p4 → p2) ∧ (p1 → p6))) → (((p2 → p6) → (False → p5)) ∨ ((False → False) ∨ (p0 ∧ p0)))) → False) → False) := by
  intro assump_5
  have assump_27 : ((((True ∨ p4) → (p6 → False)) ∧ ((p4 → p2) ∧ (p1 → p6))) → (((p2 → p6) → (False → p5)) ∨ ((False → False) ∨ (p0 ∧ p0)))) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply Or.inl
        intro assump_20
        intro assump_21
        apply False.elim assump_21
  let assump_8 := assump_5 assump_27
  apply False.elim assump_8


variable (p7 p1 p4 p2 p5 p0 : Prop)
theorem file72_115852 : (((((p5 → True) ∨ (p4 ∧ p7)) → ((p0 → p2) → False)) ∧ (((p5 ∧ False) → False) → False)) → ((((p2 → False) ∧ (False → p7)) ∨ ((p7 ∨ False) ∧ (p7 → False))) ∨ (((p1 → True) → False) → ((p5 → True) → False)))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply Or.inl
    apply Or.inl
    apply And.intro
    intro assump_16
    have assump_34 : ((p5 ∧ False) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
    let assump_20 := assump_11 assump_34
    apply False.elim assump_20
    intro assump_31
    apply False.elim assump_31


variable (p0 p4 p7 p3 p6 p5 p2 : Prop)
theorem file72_116564 : (((((True ∧ p4) → False) ∨ ((p5 ∧ p7) → (p2 → False))) ∨ (((p2 → p5) ∨ (p0 → True)) ∨ ((p5 → False) → (False → False)))) → ((((p5 → p5) → False) → False) ∨ (((p6 ∧ p2) ∨ (p3 ∨ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      have assump_70 : (p5 → p5) := by
        intro assump_12
        exact assump_12
      let assump_11 := assump_8 assump_70
      apply False.elim assump_11
    case inr assump_5 =>
      apply Or.inl
      intro assump_20
      have assump_71 : (p5 → p5) := by
        intro assump_24
        exact assump_24
      let assump_23 := assump_20 assump_71
      apply False.elim assump_23
  case inr assump_3 =>
    cases assump_3
    case inl assump_30 =>
      cases assump_30
      case inl assump_32 =>
        apply Or.inl
        intro assump_36
        have assump_72 : (p5 → p5) := by
          intro assump_40
          exact assump_40
        let assump_39 := assump_36 assump_72
        apply False.elim assump_39
      case inr assump_33 =>
        apply Or.inl
        intro assump_48
        have assump_73 : (p5 → p5) := by
          intro assump_52
          exact assump_52
        let assump_51 := assump_48 assump_73
        apply False.elim assump_51
    case inr assump_31 =>
      apply Or.inl
      intro assump_60
      have assump_74 : (p5 → p5) := by
        intro assump_64
        exact assump_64
      let assump_63 := assump_60 assump_74
      apply False.elim assump_63


variable (p0 p7 p2 p4 p1 p5 p6 : Prop)
theorem file72_118169 : ((((((p5 → p4) ∧ (p5 → p1)) → ((p6 ∨ p7) ∧ (p4 → True))) → (((p2 → False) → (True ∧ p6)) ∧ ((False → p0) ∧ (False → False)))) ∧ ((((p7 ∧ False) ∧ (p7 → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p7 ∧ False) ∧ (p7 → False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p7 p4 p3 p6 p0 p2 p5 p1 : Prop)
theorem file72_118818 : (((((p6 ∧ p5) ∧ (p1 ∧ p7)) → ((p0 → False) → (False → False))) ∨ (((p0 ∨ p4) → (p0 ∧ p1)) ∧ ((p4 → p2) ∧ (p2 → p5)))) ∨ ((((p7 → True) → (False ∨ p0)) ∧ ((p3 → p3) → (p3 ∨ p6))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_17
  intro assump_18
  intro assump_19
  apply False.elim assump_19


variable (p7 p5 p6 p0 p1 p4 p2 : Prop)
theorem file72_119188 : (((((p7 ∨ p4) ∧ (p0 ∧ p7)) → ((p1 → p5) → (False → p4))) → False) → ((((True → p2) → (p6 → p2)) → ((p6 ∧ False) → (p0 → False))) → (((p7 → False) ∧ (p1 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_23 : (((p7 ∨ p4) ∧ (p0 ∧ p7)) → ((p1 → p5) → (False → p4))) := by
      intro assump_15
      intro assump_16
      intro assump_17
      apply False.elim assump_17
    let assump_14 := assump_1 assump_23
    apply False.elim assump_14


variable (p5 p0 p2 p1 p4 p3 : Prop)
theorem file72_119781 : (((((p5 → False) ∨ (p1 ∨ False)) → ((p2 ∨ p4) → (True ∨ p3))) ∧ (((False → p3) → (True ∧ False)) ∧ ((p1 → False) ∨ (p3 → False)))) → ((((p1 ∧ p5) → (p0 ∨ p0)) ∨ ((p2 → p3) → (p4 → False))) ∧ (((p5 ∨ p5) ∧ (p0 → False)) ∧ ((p4 ∨ p2) → False)))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          have assump_194 : p1 := by
            exact assump_15
          let assump_23 := assump_10 assump_194
          apply False.elim assump_23
      case inr assump_11 =>
        apply Or.inl
        intro assump_29
        cases assump_29
        case intro assump_30 assump_31 =>
          have assump_195 : (False → p3) := by
            intro assump_40
            apply False.elim assump_40
          let assump_39 := assump_6 assump_195
          let assump_43 := And.right assump_39
          apply False.elim assump_43
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_48 assump_49 =>
    cases assump_49
    case intro assump_52 assump_53 =>
      cases assump_53
      case inl assump_56 =>
        have assump_196 : (False → p3) := by
          intro assump_62
          apply False.elim assump_62
        let assump_61 := assump_52 assump_196
        let assump_65 := And.right assump_61
        apply False.elim assump_65
      case inr assump_57 =>
        have assump_197 : (False → p3) := by
          intro assump_74
          apply False.elim assump_74
        let assump_73 := assump_52 assump_197
        let assump_77 := And.right assump_73
        apply False.elim assump_77
  intro assump_82
  cases assump_1
  case intro assump_85 assump_86 =>
    cases assump_86
    case intro assump_89 assump_90 =>
      cases assump_90
      case inl assump_93 =>
        have assump_198 : (False → p3) := by
          intro assump_99
          apply False.elim assump_99
        let assump_98 := assump_89 assump_198
        let assump_102 := And.right assump_98
        apply False.elim assump_102
      case inr assump_94 =>
        have assump_199 : (False → p3) := by
          intro assump_111
          apply False.elim assump_111
        let assump_110 := assump_89 assump_199
        let assump_114 := And.right assump_110
        apply False.elim assump_114
  intro assump_119
  cases assump_119
  case inl assump_120 =>
    cases assump_1
    case intro assump_124 assump_125 =>
      cases assump_125
      case intro assump_128 assump_129 =>
        cases assump_129
        case inl assump_132 =>
          have assump_200 : (False → p3) := by
            intro assump_138
            apply False.elim assump_138
          let assump_137 := assump_128 assump_200
          let assump_141 := And.right assump_137
          apply False.elim assump_141
        case inr assump_133 =>
          have assump_201 : (False → p3) := by
            intro assump_150
            apply False.elim assump_150
          let assump_149 := assump_128 assump_201
          let assump_153 := And.right assump_149
          apply False.elim assump_153
  case inr assump_121 =>
    cases assump_1
    case intro assump_160 assump_161 =>
      cases assump_161
      case intro assump_164 assump_165 =>
        cases assump_165
        case inl assump_168 =>
          have assump_202 : (False → p3) := by
            intro assump_174
            apply False.elim assump_174
          let assump_173 := assump_164 assump_202
          let assump_177 := And.right assump_173
          apply False.elim assump_177
        case inr assump_169 =>
          have assump_203 : (False → p3) := by
            intro assump_186
            apply False.elim assump_186
          let assump_185 := assump_164 assump_203
          let assump_189 := And.right assump_185
          apply False.elim assump_189


variable (p5 p2 : Prop)
theorem file72_123812 : (((((True → p5) → False) → ((p2 ∧ False) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((True → p5) → False) → ((p2 ∧ False) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p7 p1 p4 p6 p0 p2 : Prop)
theorem file72_124213 : (((((p1 → False) ∨ (p4 ∧ p1)) ∧ ((p3 ∨ p0) ∧ (p0 ∨ False))) → False) → ((((p2 → p2) → False) → False) ∨ (((p6 → p7) ∨ (True ∨ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (p2 → p2) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p0 p2 p1 p4 p7 p6 p3 : Prop)
theorem file72_124611 : (((((p2 ∨ p6) ∨ (p6 ∧ p0)) ∨ ((False → False) ∧ (p6 ∨ p7))) ∨ (((p2 → False) ∧ (False ∧ p6)) → ((p6 → p0) ∧ (False → False)))) ∨ ((((p7 → p1) ∨ (p6 → p4)) → ((False ∨ p3) ∧ (p3 ∨ p1))) → (((True ∧ True) ∨ (False → False)) ∨ ((p3 ∨ True) ∧ (p4 → p1))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_7
  apply And.intro
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      apply False.elim assump_15
  intro assump_19
  apply False.elim assump_19


variable (p6 p7 p3 : Prop)
theorem file72_125194 : ((((((p6 → p3) → (p7 ∨ True)) → False) → False) → False) → False) := by
  intro assump_6
  have assump_23 : ((((p6 → p3) → (p7 ∨ True)) → False) → False) := by
    intro assump_10
    have assump_24 : ((p6 → p3) → (p7 ∨ True)) := by
      intro assump_14
      apply Or.inr
      apply True.intro
    let assump_13 := assump_10 assump_24
    apply False.elim assump_13
  let assump_9 := assump_6 assump_23
  apply False.elim assump_9


variable (p4 p6 p3 p0 p7 p5 : Prop)
theorem file72_125688 : ((((((False ∨ p6) ∨ (p5 ∨ p7)) → ((p6 ∨ p4) ∧ (p0 → True))) → False) ∧ ((((p5 ∨ p3) ∧ (False ∧ p5)) → ((p7 ∧ p5) ∧ (p5 → p5))) → (((True ∨ True) ∨ (p4 → p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_65 : (((p5 ∨ p3) ∧ (False ∧ p5)) → ((p7 ∧ p5) ∧ (p5 → p5))) := by
      intro assump_9
      apply And.intro
      apply And.intro
      cases assump_9
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
      cases assump_9
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_27
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
        case inr assump_29 =>
          cases assump_27
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
      intro assump_42
      cases assump_9
      case intro assump_45 assump_46 =>
        cases assump_45
        case inl assump_47 =>
          cases assump_46
          case intro assump_51 assump_52 =>
            apply False.elim assump_51
        case inr assump_48 =>
          cases assump_46
          case intro assump_57 assump_58 =>
            apply False.elim assump_57
    let assump_8 := assump_3 assump_65
    have assump_66 : ((True ∨ True) ∨ (p4 → p5)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_61 := assump_8 assump_66
    apply False.elim assump_61


variable (p7 p2 p4 p1 p3 p6 p5 : Prop)
theorem file72_127487 : ((((((p2 ∨ p2) → False) ∧ ((True → False) → (p1 → p4))) → (((p7 ∨ p6) ∨ (p2 ∨ p5)) ∨ ((p6 → p3) → (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 ∨ p2) → False) ∧ ((True → False) → (p1 → p4))) → (((p7 ∨ p6) ∨ (p2 ∨ p5)) ∨ ((p6 → p3) → (True ∨ True)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p0 p4 p2 p7 p5 p1 p3 : Prop)
theorem file72_128069 : (((((False → False) → False) ∧ ((p6 ∨ p5) ∧ (p0 → False))) ∧ (((True → False) ∨ (p1 → False)) ∧ ((p2 ∧ p1) → False))) → ((((p4 ∨ p3) ∨ (p5 → p7)) → ((False ∨ False) → (False → p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_6
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              have assump_79 : True := by
                apply True.intro
              let assump_28 := assump_21 assump_79
              apply False.elim assump_28
            case inr assump_22 =>
              have assump_80 : (False → False) := by
                intro assump_41
                apply False.elim assump_41
              let assump_40 := assump_7 assump_80
              apply False.elim assump_40
        case inr assump_14 =>
          cases assump_6
          case intro assump_51 assump_52 =>
            cases assump_51
            case inl assump_53 =>
              have assump_81 : True := by
                apply True.intro
              let assump_60 := assump_53 assump_81
              apply False.elim assump_60
            case inr assump_54 =>
              have assump_82 : (False → False) := by
                intro assump_73
                apply False.elim assump_73
              let assump_72 := assump_7 assump_82
              apply False.elim assump_72


variable (p0 p3 p4 p2 p7 p6 : Prop)
theorem file72_129714 : ((((((p4 → False) → (p4 → False)) → False) ∧ (((False ∧ p3) ∧ (p2 → False)) ∧ ((p6 → True) ∧ (True → False)))) ∧ ((((True ∨ p6) ∨ (p0 → p2)) ∨ ((p0 ∧ p6) ∨ (p0 ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p1 p2 p7 : Prop)
theorem file72_130314 : ((((((p1 → False) ∧ (True → False)) ∧ ((False → False) ∨ (p2 ∧ p7))) → False) → False) → False) := by
  intro assump_18
  have assump_55 : ((((p1 → False) ∧ (True → False)) ∧ ((False → False) ∨ (p2 ∧ p7))) → False) := by
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_24
        case inl assump_31 =>
          have assump_56 : True := by
            apply True.intro
          let assump_36 := assump_26 assump_56
          apply False.elim assump_36
        case inr assump_32 =>
          cases assump_32
          case intro assump_40 assump_41 =>
            have assump_57 : True := by
              apply True.intro
            let assump_48 := assump_26 assump_57
            apply False.elim assump_48
  let assump_21 := assump_18 assump_55
  apply False.elim assump_21


theorem file72_131231 : (((((True ∨ False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ False) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


