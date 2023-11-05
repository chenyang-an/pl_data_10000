variable (p7 p5 p2 p1 p4 : Prop)
theorem file39_41 : ((((((True ∧ True) → (True ∨ p1)) → False) → (((False ∧ p5) ∨ (p2 → p4)) → ((p2 → p7) ∨ (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((True ∧ True) → (True ∨ p1)) → False) → (((False ∧ p5) ∨ (p2 → p4)) → ((p2 → p7) ∨ (True ∧ True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_8 =>
      apply Or.inl
      intro assump_17
      have assump_36 : ((True ∧ True) → (True ∨ p1)) := by
        intro assump_22
        cases assump_22
        case intro assump_23 assump_24 =>
          apply Or.inl
          apply True.intro
      let assump_21 := assump_5 assump_36
      apply False.elim assump_21
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p5 p6 p1 p2 p0 p4 p7 : Prop)
theorem file39_959 : (((((False → p7) ∨ (p5 → False)) → False) → (((True → False) ∧ (p7 → False)) ∨ ((False → False) ∧ (p0 ∧ p6)))) ∨ ((((False ∧ p7) ∨ (True ∨ p2)) → False) → (((False ∧ p0) → (p5 ∨ p4)) ∨ ((p1 ∧ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_25 : ((False → p7) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_25
  apply False.elim assump_7
  intro assump_14
  have assump_26 : ((False → p7) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_19
    apply False.elim assump_19
  let assump_18 := assump_1 assump_26
  apply False.elim assump_18


variable (p4 p7 p2 p3 p1 p0 p5 p6 : Prop)
theorem file39_1715 : ((((((p4 → False) → (True → p1)) ∨ ((False ∨ p4) ∨ (p6 → p4))) → (((p0 ∧ p7) → False) ∨ ((p6 → p2) ∨ (False → False)))) ∧ ((((p2 ∨ p2) ∨ (p3 ∨ p7)) ∧ ((p3 ∨ p4) → False)) ∧ (((p5 ∧ p4) ∨ (p0 → p4)) ∧ ((p5 ∧ p3) ∨ (p6 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_19
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      have assump_312 : (p3 ∨ p4) := by
                        apply Or.inl
                        exact assump_31
                      let assump_40 := assump_9 assump_312
                      apply False.elim assump_40
                  case inr assump_29 =>
                    cases assump_29
                    case intro assump_44 assump_45 =>
                      have assump_313 : (p3 ∨ p4) := by
                        apply Or.inr
                        exact assump_45
                      let assump_54 := assump_9 assump_313
                      apply False.elim assump_54
              case inr assump_21 =>
                cases assump_19
                case inl assump_60 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    have assump_314 : (p3 ∨ p4) := by
                      apply Or.inl
                      exact assump_63
                    let assump_71 := assump_9 assump_314
                    apply False.elim assump_71
                case inr assump_61 =>
                  cases assump_61
                  case intro assump_75 assump_76 =>
                    have assump_315 : (p3 ∨ p4) := by
                      apply Or.inr
                      exact assump_76
                    let assump_84 := assump_9 assump_315
                    apply False.elim assump_84
          case inr assump_13 =>
            cases assump_7
            case intro assump_92 assump_93 =>
              cases assump_92
              case inl assump_94 =>
                cases assump_94
                case intro assump_96 assump_97 =>
                  cases assump_93
                  case inl assump_102 =>
                    cases assump_102
                    case intro assump_104 assump_105 =>
                      have assump_316 : (p3 ∨ p4) := by
                        apply Or.inl
                        exact assump_105
                      let assump_114 := assump_9 assump_316
                      apply False.elim assump_114
                  case inr assump_103 =>
                    cases assump_103
                    case intro assump_118 assump_119 =>
                      have assump_317 : (p3 ∨ p4) := by
                        apply Or.inr
                        exact assump_119
                      let assump_128 := assump_9 assump_317
                      apply False.elim assump_128
              case inr assump_95 =>
                cases assump_93
                case inl assump_134 =>
                  cases assump_134
                  case intro assump_136 assump_137 =>
                    have assump_318 : (p3 ∨ p4) := by
                      apply Or.inl
                      exact assump_137
                    let assump_145 := assump_9 assump_318
                    apply False.elim assump_145
                case inr assump_135 =>
                  cases assump_135
                  case intro assump_149 assump_150 =>
                    have assump_319 : (p3 ∨ p4) := by
                      apply Or.inr
                      exact assump_150
                    let assump_158 := assump_9 assump_319
                    apply False.elim assump_158
        case inr assump_11 =>
          cases assump_11
          case inl assump_162 =>
            cases assump_7
            case intro assump_168 assump_169 =>
              cases assump_168
              case inl assump_170 =>
                cases assump_170
                case intro assump_172 assump_173 =>
                  cases assump_169
                  case inl assump_178 =>
                    cases assump_178
                    case intro assump_180 assump_181 =>
                      have assump_320 : (p3 ∨ p4) := by
                        apply Or.inl
                        exact assump_181
                      let assump_190 := assump_9 assump_320
                      apply False.elim assump_190
                  case inr assump_179 =>
                    cases assump_179
                    case intro assump_194 assump_195 =>
                      have assump_321 : (p3 ∨ p4) := by
                        apply Or.inl
                        exact assump_162
                      let assump_204 := assump_9 assump_321
                      apply False.elim assump_204
              case inr assump_171 =>
                cases assump_169
                case inl assump_210 =>
                  cases assump_210
                  case intro assump_212 assump_213 =>
                    have assump_322 : (p3 ∨ p4) := by
                      apply Or.inl
                      exact assump_213
                    let assump_221 := assump_9 assump_322
                    apply False.elim assump_221
                case inr assump_211 =>
                  cases assump_211
                  case intro assump_225 assump_226 =>
                    have assump_323 : (p3 ∨ p4) := by
                      apply Or.inl
                      exact assump_162
                    let assump_234 := assump_9 assump_323
                    apply False.elim assump_234
          case inr assump_163 =>
            cases assump_7
            case intro assump_242 assump_243 =>
              cases assump_242
              case inl assump_244 =>
                cases assump_244
                case intro assump_246 assump_247 =>
                  cases assump_243
                  case inl assump_252 =>
                    cases assump_252
                    case intro assump_254 assump_255 =>
                      have assump_324 : (p3 ∨ p4) := by
                        apply Or.inl
                        exact assump_255
                      let assump_264 := assump_9 assump_324
                      apply False.elim assump_264
                  case inr assump_253 =>
                    cases assump_253
                    case intro assump_268 assump_269 =>
                      have assump_325 : (p3 ∨ p4) := by
                        apply Or.inr
                        exact assump_269
                      let assump_278 := assump_9 assump_325
                      apply False.elim assump_278
              case inr assump_245 =>
                cases assump_243
                case inl assump_284 =>
                  cases assump_284
                  case intro assump_286 assump_287 =>
                    have assump_326 : (p3 ∨ p4) := by
                      apply Or.inl
                      exact assump_287
                    let assump_295 := assump_9 assump_326
                    apply False.elim assump_295
                case inr assump_285 =>
                  cases assump_285
                  case intro assump_299 assump_300 =>
                    have assump_327 : (p3 ∨ p4) := by
                      apply Or.inr
                      exact assump_300
                    let assump_308 := assump_9 assump_327
                    apply False.elim assump_308


variable (p6 p3 p1 p7 p0 p2 : Prop)
theorem file39_9668 : ((((((p7 ∨ False) ∧ (p1 → False)) ∨ ((p3 ∨ p7) ∨ (p7 → False))) ∧ (((False → False) → (p6 → False)) → False)) ∧ ((((False → False) → False) → ((p0 → p2) ∨ (p6 → p0))) ∧ (((True → False) ∧ (False ∨ p3)) ∧ ((p0 ∨ p7) ∧ (True → False))))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    apply False.elim assump_28
                  case inr assump_29 =>
                    cases assump_23
                    case intro assump_34 assump_35 =>
                      cases assump_34
                      case inl assump_36 =>
                        have assump_180 : True := by
                          apply True.intro
                        let assump_42 := assump_35 assump_180
                        apply False.elim assump_42
                      case inr assump_37 =>
                        have assump_181 : True := by
                          apply True.intro
                        let assump_50 := assump_35 assump_181
                        apply False.elim assump_50
          case inr assump_11 =>
            apply False.elim assump_11
      case inr assump_7 =>
        cases assump_7
        case inl assump_56 =>
          cases assump_56
          case inl assump_58 =>
            cases assump_3
            case intro assump_64 assump_65 =>
              cases assump_65
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  cases assump_71
                  case inl assump_74 =>
                    apply False.elim assump_74
                  case inr assump_75 =>
                    cases assump_69
                    case intro assump_80 assump_81 =>
                      cases assump_80
                      case inl assump_82 =>
                        have assump_182 : True := by
                          apply True.intro
                        let assump_88 := assump_81 assump_182
                        apply False.elim assump_88
                      case inr assump_83 =>
                        have assump_183 : True := by
                          apply True.intro
                        let assump_96 := assump_81 assump_183
                        apply False.elim assump_96
          case inr assump_59 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_105
              case intro assump_108 assump_109 =>
                cases assump_108
                case intro assump_110 assump_111 =>
                  cases assump_111
                  case inl assump_114 =>
                    apply False.elim assump_114
                  case inr assump_115 =>
                    cases assump_109
                    case intro assump_120 assump_121 =>
                      cases assump_120
                      case inl assump_122 =>
                        have assump_184 : True := by
                          apply True.intro
                        let assump_128 := assump_121 assump_184
                        apply False.elim assump_128
                      case inr assump_123 =>
                        have assump_185 : True := by
                          apply True.intro
                        let assump_136 := assump_121 assump_185
                        apply False.elim assump_136
        case inr assump_57 =>
          cases assump_3
          case intro assump_144 assump_145 =>
            cases assump_145
            case intro assump_148 assump_149 =>
              cases assump_148
              case intro assump_150 assump_151 =>
                cases assump_151
                case inl assump_154 =>
                  apply False.elim assump_154
                case inr assump_155 =>
                  cases assump_149
                  case intro assump_160 assump_161 =>
                    cases assump_160
                    case inl assump_162 =>
                      have assump_186 : True := by
                        apply True.intro
                      let assump_168 := assump_161 assump_186
                      apply False.elim assump_168
                    case inr assump_163 =>
                      have assump_187 : True := by
                        apply True.intro
                      let assump_176 := assump_161 assump_187
                      apply False.elim assump_176


variable (p0 p7 p1 p2 : Prop)
theorem file39_14649 : (((((True → False) → (True → False)) → False) → False) ∨ ((((p2 ∧ True) → False) → False) → (((p1 → False) → False) ∨ ((p2 ∧ p2) ∧ (p0 ∨ p7))))) := by
  apply Or.inl
  intro assump_5
  have assump_22 : ((True → False) → (True → False)) := by
    intro assump_9
    intro assump_10
    have assump_23 : True := by
      apply True.intro
    let assump_15 := assump_9 assump_23
    apply False.elim assump_15
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p6 p3 p7 p4 p5 p2 p1 p0 : Prop)
theorem file39_15187 : (((((False → False) → False) ∧ ((p6 → False) → (p3 → False))) ∨ (((p2 → False) → False) → ((False ∨ p4) → False))) → ((((False ∧ p0) ∨ (p6 → False)) → ((p6 ∧ p5) → False)) ∨ (((p7 ∨ p7) ∨ (True ∧ p5)) ∨ ((p4 → p1) → (p7 ∨ True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      cases assump_11
      case intro assump_12 assump_13 =>
        cases assump_10
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
        case inr assump_19 =>
          have assump_52 : p6 := by
            exact assump_12
          let assump_26 := assump_19 assump_52
          apply False.elim assump_26
  case inr assump_3 =>
    apply Or.inl
    intro assump_32
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      cases assump_32
      case inl assump_40 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      case inr assump_41 =>
        have assump_53 : p6 := by
          exact assump_34
        let assump_48 := assump_41 assump_53
        apply False.elim assump_48


variable (p1 p3 p7 p4 p5 p6 : Prop)
theorem file39_16522 : (((((p1 → False) → False) ∧ ((p6 ∧ p5) ∧ (p5 → False))) → False) ∨ ((((p7 → p4) → False) → ((p7 → p3) ∨ (p7 ∧ p7))) ∧ (((False → False) ∨ (False ∨ p6)) ∨ ((p4 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_20 : p5 := by
          exact assump_9
        let assump_16 := assump_7 assump_20
        apply False.elim assump_16


variable (p2 p5 p7 p1 p4 p0 p6 p3 : Prop)
theorem file39_17109 : (((((p2 ∨ p7) ∨ (p7 ∧ p1)) → ((p7 ∧ False) → (p3 ∨ p1))) ∧ (((p1 ∧ p7) ∧ (p1 → p4)) → False)) → ((((p0 ∧ p7) ∧ (p3 ∧ False)) ∧ ((p5 → False) ∨ (p1 → p5))) → (((p1 → p6) → False) ∨ ((p0 ∨ p4) ∧ (True → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case intro assump_13 assump_14 =>
          apply False.elim assump_14


variable (p1 p6 p7 p2 p5 p4 p3 : Prop)
theorem file39_17690 : (((((False ∨ p6) → (p1 ∨ p6)) ∨ ((p6 ∧ True) ∨ (p4 → p1))) ∨ (((p2 → p3) ∧ (p5 → False)) ∧ ((p4 ∨ p2) → False))) ∨ ((((p4 → False) ∨ (p5 → p7)) ∧ ((p1 → p3) ∧ (False → True))) ∨ (((p6 → False) ∧ (p2 → False)) → ((p5 → p1) ∨ (False ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply False.elim assump_2
  case inr assump_3 =>
    apply Or.inr
    exact assump_3


variable (p5 p3 p7 p4 p1 p6 p2 : Prop)
theorem file39_18194 : ((((((True → False) → False) → False) ∧ (((p6 ∨ p4) ∨ (False → p2)) → ((p3 → p3) → (p5 ∧ p6)))) ∨ ((((p7 → p3) → (p1 → False)) ∨ ((p5 ∧ True) ∨ (p3 ∧ p6))) ∧ (((p2 ∧ False) → (p4 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_91 : ((True → False) → False) := by
        intro assump_22
        have assump_92 : True := by
          apply True.intro
        let assump_25 := assump_22 assump_92
        apply False.elim assump_25
      let assump_21 := assump_4 assump_91
      apply False.elim assump_21
  case inr assump_3 =>
    cases assump_3
    case intro assump_32 assump_33 =>
      cases assump_32
      case inl assump_34 =>
        have assump_93 : ((p2 ∧ False) → (p4 ∨ True)) := by
          intro assump_41
          cases assump_41
          case intro assump_42 assump_43 =>
            apply False.elim assump_43
        let assump_40 := assump_33 assump_93
        apply False.elim assump_40
      case inr assump_35 =>
        cases assump_35
        case inl assump_51 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            have assump_94 : ((p2 ∧ False) → (p4 ∨ True)) := by
              intro assump_62
              cases assump_62
              case intro assump_63 assump_64 =>
                apply False.elim assump_64
            let assump_61 := assump_33 assump_94
            apply False.elim assump_61
        case inr assump_52 =>
          cases assump_52
          case intro assump_72 assump_73 =>
            have assump_95 : ((p2 ∧ False) → (p4 ∨ True)) := by
              intro assump_81
              cases assump_81
              case intro assump_82 assump_83 =>
                apply False.elim assump_83
            let assump_80 := assump_33 assump_95
            apply False.elim assump_80


variable (p1 p0 p4 p3 p5 p6 p2 : Prop)
theorem file39_20142 : (((((p5 → False) ∧ (p1 ∨ p5)) ∨ ((p2 → p3) ∧ (p3 → False))) → (((p4 ∨ True) → False) ∧ ((p3 ∧ True) → (p0 → False)))) → ((((p3 → False) ∨ (False → p4)) → ((True → False) → False)) ∨ (((p3 → p4) ∨ (p6 ∨ p6)) → False))) := by
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


variable (p5 p6 p4 p7 p0 p1 : Prop)
theorem file39_20807 : ((((((p7 → p4) → (p4 ∨ p5)) → ((p5 → False) ∧ (p0 → False))) ∨ (((p0 ∨ p6) → (p4 ∨ p7)) → False)) ∧ ((((True → p6) ∧ (True ∧ p0)) ∧ ((True → False) ∧ (p7 → True))) ∧ (((p1 ∨ p6) → False) ∧ ((p5 ∨ p7) → False)))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_20
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_30
            case intro assump_33 assump_34 =>
              cases assump_28
              case intro assump_39 assump_40 =>
                cases assump_26
                case intro assump_45 assump_46 =>
                  have assump_93 : True := by
                    apply True.intro
                  let assump_54 := assump_39 assump_93
                  apply False.elim assump_54
    case inr assump_22 =>
      cases assump_20
      case intro assump_60 assump_61 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_62
          case intro assump_64 assump_65 =>
            cases assump_65
            case intro assump_68 assump_69 =>
              cases assump_63
              case intro assump_74 assump_75 =>
                cases assump_61
                case intro assump_80 assump_81 =>
                  have assump_94 : True := by
                    apply True.intro
                  let assump_89 := assump_74 assump_94
                  apply False.elim assump_89


variable (p4 p7 p6 p5 p0 p2 p3 p1 : Prop)
theorem file39_22474 : ((((((p4 → p3) ∨ (p2 → p2)) ∧ ((p6 ∨ p3) ∧ (p2 → False))) → (((p2 → p1) → (p3 ∨ p0)) → False)) ∧ ((((p3 ∨ True) ∧ (True → False)) → ((p0 ∧ p5) ∨ (False ∨ p7))) ∧ (((p0 ∧ p2) ∧ (False ∧ p5)) ∧ ((p3 ∧ p2) → (p3 → p1))))) → False) := by
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
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p0 p2 p5 p4 p3 : Prop)
theorem file39_23200 : (((((False ∧ p4) ∧ (p2 → p2)) ∧ ((p5 → p3) ∧ (p3 → p5))) → False) ∨ ((((p3 ∨ False) → False) ∨ ((p0 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_6


variable (p4 p5 p6 p1 p7 p3 p0 : Prop)
theorem file39_23629 : (((((p7 → False) ∧ (p6 ∨ True)) ∧ ((p7 ∧ False) ∨ (p6 ∨ True))) ∧ (((p4 → False) ∧ (p0 → p7)) → False)) → ((((p4 ∨ True) → False) → ((p1 ∨ p5) ∨ (p3 → p3))) ∨ (((False → p7) → False) ∨ ((p4 → False) ∧ (True ∧ p7))))) := by
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_28
        case inl assump_31 =>
          cases assump_26
          case inl assump_35 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              apply False.elim assump_38
          case inr assump_36 =>
            cases assump_36
            case inl assump_43 =>
              apply Or.inl
              intro assump_49
              apply Or.inr
              intro assump_52
              exact assump_52
            case inr assump_44 =>
              apply Or.inl
              intro assump_59
              apply Or.inr
              intro assump_62
              exact assump_62
        case inr assump_32 =>
          cases assump_26
          case inl assump_67 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              apply False.elim assump_70
          case inr assump_68 =>
            cases assump_68
            case inl assump_75 =>
              apply Or.inl
              intro assump_81
              apply Or.inr
              intro assump_84
              exact assump_84
            case inr assump_76 =>
              apply Or.inl
              intro assump_91
              apply Or.inr
              intro assump_94
              exact assump_94


variable (p1 p5 p0 p2 p3 : Prop)
theorem file39_25363 : (((((False → p0) → (p1 → False)) → ((True ∨ p2) → (p2 → False))) ∨ (((p1 ∧ p3) ∧ (p3 ∧ False)) ∧ ((p3 → False) ∨ (p1 ∨ p2)))) → ((((p3 ∧ p0) ∨ (p0 ∨ False)) ∧ ((p2 ∨ False) → False)) ∨ (((p5 ∧ p1) ∧ (p1 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_37 : p1 := by
          exact assump_10
        let assump_17 := assump_8 assump_37
        apply False.elim assump_17
  case inr assump_3 =>
    cases assump_3
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_24
          case intro assump_31 assump_32 =>
            apply False.elim assump_32


variable (p7 p2 p4 p0 p5 p6 p1 : Prop)
theorem file39_26320 : ((((((p1 ∨ p0) ∧ (p7 ∧ p4)) ∧ ((p6 ∧ p2) → (p7 → False))) ∨ (((p7 → False) ∧ (True → False)) → False)) ∧ ((((True → False) ∨ (p0 ∨ p7)) ∨ ((True ∨ p1) → (p4 → p4))) ∧ (((p7 ∨ p5) ∨ (p2 → True)) → False))) → False) := by
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
          case inl assump_10 =>
            cases assump_9
            case intro assump_14 assump_15 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case inl assump_26 =>
                    have assump_157 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                      apply Or.inl
                      apply Or.inl
                      exact assump_14
                    let assump_32 := assump_23 assump_157
                    apply False.elim assump_32
                  case inr assump_27 =>
                    cases assump_27
                    case inl assump_36 =>
                      have assump_158 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_14
                      let assump_42 := assump_23 assump_158
                      apply False.elim assump_42
                    case inr assump_37 =>
                      have assump_159 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_37
                      let assump_50 := assump_23 assump_159
                      apply False.elim assump_50
                case inr assump_25 =>
                  have assump_160 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_14
                  let assump_58 := assump_23 assump_160
                  apply False.elim assump_58
          case inr assump_11 =>
            cases assump_9
            case intro assump_64 assump_65 =>
              cases assump_3
              case intro assump_72 assump_73 =>
                cases assump_72
                case inl assump_74 =>
                  cases assump_74
                  case inl assump_76 =>
                    have assump_161 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                      apply Or.inl
                      apply Or.inl
                      exact assump_64
                    let assump_82 := assump_73 assump_161
                    apply False.elim assump_82
                  case inr assump_77 =>
                    cases assump_77
                    case inl assump_86 =>
                      have assump_162 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_64
                      let assump_92 := assump_73 assump_162
                      apply False.elim assump_92
                    case inr assump_87 =>
                      have assump_163 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_87
                      let assump_100 := assump_73 assump_163
                      apply False.elim assump_100
                case inr assump_75 =>
                  have assump_164 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                    apply Or.inl
                    apply Or.inl
                    exact assump_64
                  let assump_108 := assump_73 assump_164
                  apply False.elim assump_108
    case inr assump_5 =>
      cases assump_3
      case intro assump_114 assump_115 =>
        cases assump_114
        case inl assump_116 =>
          cases assump_116
          case inl assump_118 =>
            have assump_165 : ((p7 ∨ p5) ∨ (p2 → True)) := by
              apply Or.inr
              intro assump_125
              apply True.intro
            let assump_124 := assump_115 assump_165
            apply False.elim assump_124
          case inr assump_119 =>
            cases assump_119
            case inl assump_129 =>
              have assump_166 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                apply Or.inr
                intro assump_136
                apply True.intro
              let assump_135 := assump_115 assump_166
              apply False.elim assump_135
            case inr assump_130 =>
              have assump_167 : ((p7 ∨ p5) ∨ (p2 → True)) := by
                apply Or.inl
                apply Or.inl
                exact assump_130
              let assump_144 := assump_115 assump_167
              apply False.elim assump_144
        case inr assump_117 =>
          have assump_168 : ((p7 ∨ p5) ∨ (p2 → True)) := by
            apply Or.inr
            intro assump_153
            apply True.intro
          let assump_152 := assump_115 assump_168
          apply False.elim assump_152


variable (p2 p1 p0 p3 p4 p6 p5 p7 : Prop)
theorem file39_31552 : (((((p7 ∨ False) ∨ (p2 ∧ p5)) ∧ ((p5 ∨ p6) → False)) ∧ (((p3 → p6) → False) ∨ ((p5 → False) → (p1 ∨ p0)))) ∨ ((((True → False) ∨ (p0 → False)) ∧ ((p3 ∨ True) → False)) → (((p4 ∧ p6) ∧ (p1 ∧ p0)) → False))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            have assump_37 : (p3 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_25 := assump_18 assump_37
            apply False.elim assump_25
          case inr assump_20 =>
            have assump_38 : (p3 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_33 := assump_18 assump_38
            apply False.elim assump_33


variable (p4 p6 p5 p1 p2 p7 p3 : Prop)
theorem file39_32584 : ((((((p6 → p1) ∧ (False ∨ False)) → ((p4 → False) → (p7 ∨ p2))) → (((False → False) ∧ (False ∧ p2)) → ((p5 → True) → (p3 ∧ p4)))) → False) → False) := by
  intro assump_19
  have assump_49 : ((((p6 → p1) ∧ (False ∨ False)) → ((p4 → False) → (p7 ∨ p2))) → (((False → False) ∧ (False ∧ p2)) → ((p5 → True) → (p3 ∧ p4)))) := by
    intro assump_23
    intro assump_24
    intro assump_25
    apply And.intro
    cases assump_24
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        apply False.elim assump_32
    cases assump_24
    case intro assump_38 assump_39 =>
      cases assump_39
      case intro assump_42 assump_43 =>
        apply False.elim assump_42
  let assump_22 := assump_19 assump_49
  apply False.elim assump_22


variable (p5 p1 p3 : Prop)
theorem file39_33418 : (((((True ∧ False) → False) → False) ∧ (((p1 ∨ True) → False) ∨ ((p5 ∨ p3) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_28 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_10 := assump_6 assump_28
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_29 : ((True ∧ False) → False) := by
        intro assump_18
        cases assump_18
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
      let assump_17 := assump_2 assump_29
      apply False.elim assump_17


variable (p3 p7 p5 p6 p2 : Prop)
theorem file39_34131 : (((((p5 ∧ False) ∨ (False ∨ False)) → ((False → False) ∨ (p3 ∧ p6))) ∨ (((p2 ∧ p7) ∧ (False ∧ p7)) ∨ ((True ∧ p3) → False))) ∨ ((((True ∨ p3) → False) → ((p7 → False) → False)) ∨ (((p7 → p2) → (p7 → False)) ∧ ((p6 ∧ False) → (p5 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply False.elim assump_11


variable (p7 p5 p1 p0 p2 p4 p3 : Prop)
theorem file39_34776 : ((((((p1 ∧ p4) ∧ (False ∨ p4)) → ((False → p7) → False)) ∧ (((p0 ∧ False) → False) → False)) ∧ ((((p1 ∧ p2) ∧ (p5 ∨ True)) → ((False ∨ False) ∨ (p0 ∧ p2))) ∨ (((p1 ∧ p4) → (p1 ∨ p2)) ∨ ((p3 ∨ p1) ∨ (p0 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_104 : ((p0 ∧ False) → False) := by
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
        let assump_15 := assump_5 assump_104
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case inl assump_26 =>
          have assump_105 : ((p0 ∧ False) → False) := by
            intro assump_32
            cases assump_32
            case intro assump_33 assump_34 =>
              apply False.elim assump_34
          let assump_31 := assump_5 assump_105
          apply False.elim assump_31
        case inr assump_27 =>
          cases assump_27
          case inl assump_42 =>
            cases assump_42
            case inl assump_44 =>
              have assump_106 : ((p0 ∧ False) → False) := by
                intro assump_50
                cases assump_50
                case intro assump_51 assump_52 =>
                  apply False.elim assump_52
              let assump_49 := assump_5 assump_106
              apply False.elim assump_49
            case inr assump_45 =>
              have assump_107 : ((p0 ∧ False) → False) := by
                intro assump_64
                cases assump_64
                case intro assump_65 assump_66 =>
                  apply False.elim assump_66
              let assump_63 := assump_5 assump_107
              apply False.elim assump_63
          case inr assump_43 =>
            cases assump_43
            case inl assump_74 =>
              have assump_108 : ((p0 ∧ False) → False) := by
                intro assump_80
                cases assump_80
                case intro assump_81 assump_82 =>
                  apply False.elim assump_82
              let assump_79 := assump_5 assump_108
              apply False.elim assump_79
            case inr assump_75 =>
              have assump_109 : ((p0 ∧ False) → False) := by
                intro assump_94
                cases assump_94
                case intro assump_95 assump_96 =>
                  apply False.elim assump_96
              let assump_93 := assump_5 assump_109
              apply False.elim assump_93


variable (p7 p5 p3 p4 : Prop)
theorem file39_37425 : (((((p3 ∧ p5) ∧ (False ∧ True)) → False) → False) → ((((p5 ∨ True) ∨ (p4 → False)) → False) ∨ (((p7 ∧ p5) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_68 : (((p3 ∧ p5) ∧ (False ∧ True)) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              apply False.elim assump_22
      let assump_12 := assump_1 assump_68
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_69 : (((p3 ∧ p5) ∧ (False ∧ True)) → False) := by
        intro assump_32
        cases assump_32
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            cases assump_34
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
      let assump_31 := assump_1 assump_69
      apply False.elim assump_31
  case inr assump_6 =>
    have assump_70 : (((p3 ∧ p5) ∧ (False ∧ True)) → False) := by
      intro assump_52
      cases assump_52
      case intro assump_53 assump_54 =>
        cases assump_53
        case intro assump_55 assump_56 =>
          cases assump_54
          case intro assump_61 assump_62 =>
            apply False.elim assump_61
    let assump_51 := assump_1 assump_70
    apply False.elim assump_51


variable (p0 p4 p2 p6 p5 : Prop)
theorem file39_39027 : (((((p4 → False) → (p4 → True)) ∨ ((p2 ∧ p4) → (False → False))) → (((p2 ∧ p0) ∧ (p5 → False)) → False)) → ((((p6 ∧ False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_22 : ((p6 ∧ False) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_11 := assump_2 assump_22
  apply False.elim assump_11


variable (p5 p4 p2 p6 p1 : Prop)
theorem file39_39501 : ((((((p5 → p1) ∨ (p2 ∧ True)) → ((p4 → False) ∨ (p6 ∧ p5))) → (((p5 → p1) → False) → ((False → False) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 → p1) ∨ (p2 ∧ True)) → ((p4 → False) ∨ (p6 ∧ p5))) → (((p5 → p1) → False) → ((False → False) ∨ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p5 p4 p0 p1 p2 p7 p3 : Prop)
theorem file39_40042 : (((((True ∧ p4) → (True ∧ True)) ∨ ((p5 ∨ True) → (p1 ∨ p6))) ∨ (((p3 → False) ∧ (p1 ∧ p5)) ∨ ((p0 → p6) → (p6 ∨ False)))) ∨ ((((p2 ∧ p7) → False) → ((p1 → False) → False)) → (((p6 → False) ∧ (p1 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_14
  apply And.intro
  apply True.intro
  apply True.intro


variable (p5 p4 p3 p1 p2 p6 p7 p0 : Prop)
theorem file39_40450 : (((((p0 ∧ p0) → (p3 ∧ False)) → ((p5 → p4) → (p5 → p2))) → False) → ((((p0 → False) ∧ (p2 ∧ p6)) ∨ ((True ∧ p7) → (p5 → False))) → (((p7 ∧ p2) → False) ∨ ((p1 → False) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          have assump_65 : (((p0 ∧ p0) → (p3 ∧ False)) → ((p5 → p4) → (p5 → p2))) := by
            intro assump_27
            intro assump_28
            intro assump_29
            exact assump_19
          let assump_26 := assump_1 assump_65
          apply False.elim assump_26
  case inr assump_4 =>
    apply Or.inl
    intro assump_43
    cases assump_43
    case intro assump_44 assump_45 =>
      have assump_66 : (((p0 ∧ p0) → (p3 ∧ False)) → ((p5 → p4) → (p5 → p2))) := by
        intro assump_53
        intro assump_54
        intro assump_55
        exact assump_45
      let assump_52 := assump_1 assump_66
      apply False.elim assump_52


variable (p0 p2 p3 p6 p5 p7 p1 : Prop)
theorem file39_41662 : (((((p7 ∨ p5) ∧ (p6 → p2)) → ((p2 → p6) ∧ (p0 → False))) → (((False → p7) → False) → ((p2 ∧ p3) → False))) ∨ ((((p5 ∨ p5) ∨ (p1 → False)) → ((False → p0) ∧ (p1 → False))) ∧ (((False ∨ p5) → (True → p2)) → ((True ∨ False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_22 : (False → p7) := by
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_2 assump_22
    apply False.elim assump_15


variable (p1 p4 p3 p2 p5 p6 : Prop)
theorem file39_42244 : (((((p2 ∨ p5) → False) → ((p6 ∧ False) → False)) → False) → ((((p1 → False) ∧ (False → False)) ∧ ((p3 → False) → (p4 → False))) ∨ (((False ∧ True) ∧ (p5 ∨ p5)) → ((True ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply And.intro
  intro assump_4
  have assump_43 : (((p2 ∨ p5) → False) → ((p6 ∧ False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
  let assump_8 := assump_1 assump_43
  apply False.elim assump_8
  intro assump_20
  apply False.elim assump_20
  intro assump_23
  intro assump_24
  have assump_44 : (((p2 ∨ p5) → False) → ((p6 ∧ False) → False)) := by
    intro assump_32
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      apply False.elim assump_35
  let assump_31 := assump_1 assump_44
  apply False.elim assump_31


variable (p5 p0 p3 p6 p1 : Prop)
theorem file39_43199 : (((((p5 ∨ p3) ∧ (p1 ∧ p6)) → ((False ∨ p1) ∨ (p5 ∧ p1))) ∧ (((False ∧ p0) ∧ (False → False)) ∧ ((False ∧ p0) ∨ (p6 → False)))) → ((((p6 ∧ p5) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13


variable (p0 p4 p7 p6 p1 p2 : Prop)
theorem file39_43740 : ((((((p7 ∧ p6) ∧ (p7 ∧ True)) ∨ ((p4 → False) → (p2 ∨ p1))) → False) ∧ ((((True ∨ p4) ∨ (True ∧ p0)) ∨ ((p6 → False) ∨ (True ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((True ∨ p4) ∨ (True ∧ p0)) ∨ ((p6 → False) ∨ (True ∧ p2))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p1 p5 p4 p6 p0 p2 : Prop)
theorem file39_44266 : (((((p2 ∨ p2) → False) ∧ ((p5 → False) ∧ (p2 ∧ p4))) ∨ (((p6 → p6) ∧ (False ∨ p0)) → False)) → ((((p0 ∧ p1) → (p1 → False)) ∨ ((p2 ∨ True) ∧ (p3 ∧ False))) → (((p0 → False) ∧ (p6 ∨ False)) → ((p3 ∨ True) ∨ (p0 ∨ p5))))) := by
  intro assump_26
  intro assump_27
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_30
    case inl assump_33 =>
      cases assump_27
      case inl assump_37 =>
        cases assump_26
        case inl assump_41 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            cases assump_44
            case intro assump_47 assump_48 =>
              cases assump_48
              case intro assump_51 assump_52 =>
                apply Or.inl
                apply Or.inr
                apply True.intro
        case inr assump_42 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_38 =>
        cases assump_38
        case intro assump_59 assump_60 =>
          cases assump_59
          case inl assump_61 =>
            cases assump_60
            case intro assump_65 assump_66 =>
              apply False.elim assump_66
          case inr assump_62 =>
            cases assump_60
            case intro assump_73 assump_74 =>
              apply False.elim assump_74
    case inr assump_34 =>
      apply False.elim assump_34


variable (p4 p2 p0 p5 p6 p7 p3 : Prop)
theorem file39_45702 : ((((((p5 → p0) → (p4 ∧ p2)) ∨ ((p6 → False) ∧ (p0 ∧ p7))) → False) ∧ ((((False ∧ p5) ∧ (p3 → p5)) → ((p6 ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((False ∧ p5) ∧ (p3 → p5)) → ((p6 ∧ p2) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        cases assump_9
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p3 p0 p5 p2 : Prop)
theorem file39_46396 : ((((((p2 → False) ∧ (p5 ∧ p3)) ∧ ((p0 → p5) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p2 → False) ∧ (p5 ∧ p3)) ∧ ((p0 → p5) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            have assump_32 : True := by
              apply True.intro
            let assump_24 := assump_19 assump_32
            apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p5 p7 p2 p0 p4 p6 p3 : Prop)
theorem file39_47161 : ((((((p7 ∨ p7) → (p3 → p2)) → False) ∧ (((p0 ∧ p6) ∨ (p5 ∨ p2)) → ((p0 ∨ False) → False))) ∧ ((((p2 ∧ p7) ∧ (True → False)) ∨ ((True → False) ∧ (p4 → False))) ∧ (((p2 ∧ p1) → (p6 ∧ p4)) ∨ ((p7 ∨ p1) → (False → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_11
              case inl assump_24 =>
                have assump_65 : True := by
                  apply True.intro
                let assump_29 := assump_15 assump_65
                apply False.elim assump_29
              case inr assump_25 =>
                have assump_66 : True := by
                  apply True.intro
                let assump_37 := assump_15 assump_66
                apply False.elim assump_37
        case inr assump_13 =>
          cases assump_13
          case intro assump_41 assump_42 =>
            cases assump_11
            case inl assump_47 =>
              have assump_67 : True := by
                apply True.intro
              let assump_53 := assump_41 assump_67
              apply False.elim assump_53
            case inr assump_48 =>
              have assump_68 : True := by
                apply True.intro
              let assump_61 := assump_41 assump_68
              apply False.elim assump_61


variable (p0 p6 p3 p7 p2 p4 p5 : Prop)
theorem file39_48821 : ((((((p5 ∧ p4) ∧ (p4 ∧ p7)) → ((True → p3) → (p3 ∨ p4))) ∨ (((p6 → p3) → (p2 → p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p5 ∧ p4) ∧ (p4 ∧ p7)) → ((True → p3) → (p3 ∨ p4))) ∨ (((p6 → p3) → (p2 → p0)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply Or.inr
          exact assump_17
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p6 p2 : Prop)
theorem file39_49476 : (((((p6 → p2) → False) → ((p2 → False) ∨ (True → False))) ∧ (((False ∧ p7) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : ((False ∧ p7) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p2 p3 p1 p5 p4 p0 : Prop)
theorem file39_49949 : (((((True → False) → (True ∨ False)) ∧ ((p4 ∧ False) ∨ (False ∧ p2))) → False) ∨ ((((p5 → p4) ∧ (True ∨ True)) → ((p5 → False) → (p2 → False))) ∧ (((True ∨ p2) → (p3 ∧ p4)) → ((p4 ∧ p0) ∧ (True ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p1 p3 p6 p4 p5 p0 p2 : Prop)
theorem file39_50563 : (((((p5 ∧ p4) → False) ∨ ((p4 ∨ p4) ∨ (p5 ∧ p3))) → (((p0 ∧ p2) ∧ (p3 ∨ p1)) → ((True → False) → (p2 → p6)))) ∨ ((((p6 → False) → (p4 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_10
      case inl assump_17 =>
        cases assump_1
        case inl assump_21 =>
          have assump_125 : True := by
            apply True.intro
          let assump_29 := assump_3 assump_125
          apply False.elim assump_29
        case inr assump_22 =>
          cases assump_22
          case inl assump_33 =>
            cases assump_33
            case inl assump_35 =>
              have assump_126 : True := by
                apply True.intro
              let assump_43 := assump_3 assump_126
              apply False.elim assump_43
            case inr assump_36 =>
              have assump_127 : True := by
                apply True.intro
              let assump_53 := assump_3 assump_127
              apply False.elim assump_53
          case inr assump_34 =>
            cases assump_34
            case intro assump_57 assump_58 =>
              have assump_128 : True := by
                apply True.intro
              let assump_68 := assump_3 assump_128
              apply False.elim assump_68
      case inr assump_18 =>
        cases assump_1
        case inl assump_74 =>
          have assump_129 : True := by
            apply True.intro
          let assump_82 := assump_3 assump_129
          apply False.elim assump_82
        case inr assump_75 =>
          cases assump_75
          case inl assump_86 =>
            cases assump_86
            case inl assump_88 =>
              have assump_130 : True := by
                apply True.intro
              let assump_96 := assump_3 assump_130
              apply False.elim assump_96
            case inr assump_89 =>
              have assump_131 : True := by
                apply True.intro
              let assump_106 := assump_3 assump_131
              apply False.elim assump_106
          case inr assump_87 =>
            cases assump_87
            case intro assump_110 assump_111 =>
              have assump_132 : True := by
                apply True.intro
              let assump_121 := assump_3 assump_132
              apply False.elim assump_121


variable (p3 p6 p5 p7 p0 : Prop)
theorem file39_53063 : ((((((p0 → False) → (p6 → p6)) ∧ ((p6 ∧ p5) → (False → False))) ∨ (((p5 → False) ∨ (p7 → False)) ∧ ((p3 ∧ False) ∨ (p0 → p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 → False) → (p6 → p6)) ∧ ((p6 ∧ p5) → (False → False))) ∨ (((p5 → False) ∨ (p7 → False)) ∧ ((p3 ∧ False) ∨ (p0 → p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    exact assump_6
    intro assump_11
    intro assump_12
    apply False.elim assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p0 p3 p5 p6 : Prop)
theorem file39_53670 : (((((False ∨ p6) → (p1 → False)) → False) ∧ (((p0 ∧ p6) ∧ (p5 → p3)) ∧ ((False ∧ p1) ∧ (True ∧ p3)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_11
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply False.elim assump_24


variable (p3 p2 p7 p1 p6 p4 : Prop)
theorem file39_54285 : ((((((p4 → False) → False) ∨ ((p4 → p4) → (False ∧ p3))) ∨ (((p3 ∧ p7) ∧ (p3 ∧ False)) → False)) ∧ ((((p4 ∧ p1) ∧ (True ∧ p2)) ∧ ((p1 → False) ∧ (p6 → False))) ∨ (((p7 → p2) ∨ (p1 ∧ p6)) ∧ ((False → p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                cases assump_15
                case intro assump_22 assump_23 =>
                  cases assump_13
                  case intro assump_28 assump_29 =>
                    have assump_191 : p1 := by
                      exact assump_17
                    let assump_35 := assump_28 assump_191
                    apply False.elim assump_35
        case inr assump_11 =>
          cases assump_11
          case intro assump_39 assump_40 =>
            cases assump_39
            case inl assump_41 =>
              have assump_192 : (False → p2) := by
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_40 assump_192
              apply False.elim assump_47
            case inr assump_42 =>
              cases assump_42
              case intro assump_54 assump_55 =>
                have assump_193 : (False → p2) := by
                  intro assump_63
                  apply False.elim assump_63
                let assump_62 := assump_40 assump_193
                apply False.elim assump_62
      case inr assump_7 =>
        cases assump_3
        case inl assump_71 =>
          cases assump_71
          case intro assump_73 assump_74 =>
            cases assump_73
            case intro assump_75 assump_76 =>
              cases assump_75
              case intro assump_77 assump_78 =>
                cases assump_76
                case intro assump_83 assump_84 =>
                  cases assump_74
                  case intro assump_89 assump_90 =>
                    have assump_194 : p1 := by
                      exact assump_78
                    let assump_96 := assump_89 assump_194
                    apply False.elim assump_96
        case inr assump_72 =>
          cases assump_72
          case intro assump_100 assump_101 =>
            cases assump_100
            case inl assump_102 =>
              have assump_195 : (False → p2) := by
                intro assump_109
                apply False.elim assump_109
              let assump_108 := assump_101 assump_195
              apply False.elim assump_108
            case inr assump_103 =>
              cases assump_103
              case intro assump_115 assump_116 =>
                have assump_196 : (False → p2) := by
                  intro assump_124
                  apply False.elim assump_124
                let assump_123 := assump_101 assump_196
                apply False.elim assump_123
    case inr assump_5 =>
      cases assump_3
      case inl assump_132 =>
        cases assump_132
        case intro assump_134 assump_135 =>
          cases assump_134
          case intro assump_136 assump_137 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              cases assump_137
              case intro assump_144 assump_145 =>
                cases assump_135
                case intro assump_150 assump_151 =>
                  have assump_197 : p1 := by
                    exact assump_139
                  let assump_157 := assump_150 assump_197
                  apply False.elim assump_157
      case inr assump_133 =>
        cases assump_133
        case intro assump_161 assump_162 =>
          cases assump_161
          case inl assump_163 =>
            have assump_198 : (False → p2) := by
              intro assump_170
              apply False.elim assump_170
            let assump_169 := assump_162 assump_198
            apply False.elim assump_169
          case inr assump_164 =>
            cases assump_164
            case intro assump_176 assump_177 =>
              have assump_199 : (False → p2) := by
                intro assump_185
                apply False.elim assump_185
              let assump_184 := assump_162 assump_199
              apply False.elim assump_184


variable (p5 p0 p4 p6 p1 p7 p2 : Prop)
theorem file39_58845 : ((((((p5 ∧ p6) ∧ (True → p4)) ∧ ((p5 → True) → False)) → (((p4 ∨ p2) → False) → ((p0 → True) ∧ (p1 → p7)))) → False) → False) := by
  intro assump_11
  have assump_45 : ((((p5 ∧ p6) ∧ (True → p4)) ∧ ((p5 → True) → False)) → (((p4 ∨ p2) → False) → ((p0 → True) ∧ (p1 → p7)))) := by
    intro assump_15
    intro assump_16
    apply And.intro
    intro assump_17
    apply True.intro
    intro assump_18
    cases assump_15
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          have assump_46 : (p5 → True) := by
            intro assump_38
            apply True.intro
          let assump_37 := assump_24 assump_46
          apply False.elim assump_37
  let assump_14 := assump_11 assump_45
  apply False.elim assump_14


variable (p1 p5 p7 p0 p6 p2 p3 p4 : Prop)
theorem file39_59753 : (((((True ∨ p0) → (p4 ∨ p5)) ∨ ((p0 → False) → (p7 → False))) → False) → ((((p5 ∨ p0) ∧ (False ∧ p3)) → ((False → False) ∧ (False → False))) ∨ (((p4 ∨ p6) → (False → False)) ∧ ((p2 → False) ∧ (p1 ∧ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  apply False.elim assump_5
  intro assump_8
  apply False.elim assump_8


variable (p5 p6 p4 p0 p1 p2 p7 : Prop)
theorem file39_60185 : (((((p5 ∨ p5) ∧ (p5 ∨ p4)) ∧ ((True ∧ p1) ∨ (p5 ∨ p2))) ∧ (((True ∨ p1) ∧ (p5 → p1)) ∧ ((p7 ∨ p6) ∧ (p7 ∧ True)))) → ((((p5 → False) ∨ (p1 → False)) ∨ ((p0 ∧ False) ∨ (p1 ∧ p6))) → (((False ∧ True) → (p5 ∧ p2)) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            cases assump_13
            case inl assump_15 =>
              cases assump_14
              case inl assump_19 =>
                cases assump_12
                case inl assump_23 =>
                  cases assump_23
                  case intro assump_25 assump_26 =>
                    cases assump_10
                    case intro assump_31 assump_32 =>
                      cases assump_31
                      case intro assump_33 assump_34 =>
                        cases assump_33
                        case inl assump_35 =>
                          cases assump_32
                          case intro assump_41 assump_42 =>
                            cases assump_41
                            case inl assump_43 =>
                              cases assump_42
                              case intro assump_47 assump_48 =>
                                apply Or.inl
                                intro assump_53
                                apply And.intro
                                cases assump_53
                                case intro assump_54 assump_55 =>
                                  apply False.elim assump_54
                                cases assump_53
                                case intro assump_58 assump_59 =>
                                  apply False.elim assump_58
                            case inr assump_44 =>
                              cases assump_42
                              case intro assump_64 assump_65 =>
                                apply Or.inl
                                intro assump_70
                                apply And.intro
                                cases assump_70
                                case intro assump_71 assump_72 =>
                                  apply False.elim assump_71
                                cases assump_70
                                case intro assump_75 assump_76 =>
                                  apply False.elim assump_75
                        case inr assump_36 =>
                          cases assump_32
                          case intro assump_83 assump_84 =>
                            cases assump_83
                            case inl assump_85 =>
                              cases assump_84
                              case intro assump_89 assump_90 =>
                                apply Or.inl
                                intro assump_95
                                apply And.intro
                                cases assump_95
                                case intro assump_96 assump_97 =>
                                  apply False.elim assump_96
                                cases assump_95
                                case intro assump_100 assump_101 =>
                                  apply False.elim assump_100
                            case inr assump_86 =>
                              cases assump_84
                              case intro assump_106 assump_107 =>
                                apply Or.inl
                                intro assump_112
                                apply And.intro
                                cases assump_112
                                case intro assump_113 assump_114 =>
                                  apply False.elim assump_113
                                cases assump_112
                                case intro assump_117 assump_118 =>
                                  apply False.elim assump_117
                case inr assump_24 =>
                  cases assump_24
                  case inl assump_121 =>
                    cases assump_10
                    case intro assump_125 assump_126 =>
                      cases assump_125
                      case intro assump_127 assump_128 =>
                        cases assump_127
                        case inl assump_129 =>
                          cases assump_126
                          case intro assump_135 assump_136 =>
                            cases assump_135
                            case inl assump_137 =>
                              cases assump_136
                              case intro assump_141 assump_142 =>
                                apply Or.inl
                                intro assump_147
                                apply And.intro
                                cases assump_147
                                case intro assump_148 assump_149 =>
                                  apply False.elim assump_148
                                cases assump_147
                                case intro assump_152 assump_153 =>
                                  apply False.elim assump_152
                            case inr assump_138 =>
                              cases assump_136
                              case intro assump_158 assump_159 =>
                                apply Or.inl
                                intro assump_164
                                apply And.intro
                                cases assump_164
                                case intro assump_165 assump_166 =>
                                  apply False.elim assump_165
                                cases assump_164
                                case intro assump_169 assump_170 =>
                                  apply False.elim assump_169
                        case inr assump_130 =>
                          cases assump_126
                          case intro assump_177 assump_178 =>
                            cases assump_177
                            case inl assump_179 =>
                              cases assump_178
                              case intro assump_183 assump_184 =>
                                apply Or.inl
                                intro assump_189
                                apply And.intro
                                cases assump_189
                                case intro assump_190 assump_191 =>
                                  apply False.elim assump_190
                                cases assump_189
                                case intro assump_194 assump_195 =>
                                  apply False.elim assump_194
                            case inr assump_180 =>
                              cases assump_178
                              case intro assump_200 assump_201 =>
                                apply Or.inl
                                intro assump_206
                                apply And.intro
                                cases assump_206
                                case intro assump_207 assump_208 =>
                                  apply False.elim assump_207
                                cases assump_206
                                case intro assump_211 assump_212 =>
                                  apply False.elim assump_211
                  case inr assump_122 =>
                    cases assump_10
                    case intro assump_217 assump_218 =>
                      cases assump_217
                      case intro assump_219 assump_220 =>
                        cases assump_219
                        case inl assump_221 =>
                          cases assump_218
                          case intro assump_227 assump_228 =>
                            cases assump_227
                            case inl assump_229 =>
                              cases assump_228
                              case intro assump_233 assump_234 =>
                                apply Or.inl
                                intro assump_239
                                apply And.intro
                                cases assump_239
                                case intro assump_240 assump_241 =>
                                  apply False.elim assump_240
                                cases assump_239
                                case intro assump_244 assump_245 =>
                                  apply False.elim assump_244
                            case inr assump_230 =>
                              cases assump_228
                              case intro assump_250 assump_251 =>
                                apply Or.inl
                                intro assump_256
                                apply And.intro
                                cases assump_256
                                case intro assump_257 assump_258 =>
                                  apply False.elim assump_257
                                cases assump_256
                                case intro assump_261 assump_262 =>
                                  apply False.elim assump_261
                        case inr assump_222 =>
                          cases assump_218
                          case intro assump_269 assump_270 =>
                            cases assump_269
                            case inl assump_271 =>
                              cases assump_270
                              case intro assump_275 assump_276 =>
                                apply Or.inl
                                intro assump_281
                                apply And.intro
                                cases assump_281
                                case intro assump_282 assump_283 =>
                                  apply False.elim assump_282
                                cases assump_281
                                case intro assump_286 assump_287 =>
                                  apply False.elim assump_286
                            case inr assump_272 =>
                              cases assump_270
                              case intro assump_292 assump_293 =>
                                apply Or.inl
                                intro assump_298
                                apply And.intro
                                cases assump_298
                                case intro assump_299 assump_300 =>
                                  apply False.elim assump_299
                                cases assump_298
                                case intro assump_303 assump_304 =>
                                  apply False.elim assump_303
              case inr assump_20 =>
                cases assump_12
                case inl assump_309 =>
                  cases assump_309
                  case intro assump_311 assump_312 =>
                    cases assump_10
                    case intro assump_317 assump_318 =>
                      cases assump_317
                      case intro assump_319 assump_320 =>
                        cases assump_319
                        case inl assump_321 =>
                          cases assump_318
                          case intro assump_327 assump_328 =>
                            cases assump_327
                            case inl assump_329 =>
                              cases assump_328
                              case intro assump_333 assump_334 =>
                                apply Or.inl
                                intro assump_339
                                apply And.intro
                                cases assump_339
                                case intro assump_340 assump_341 =>
                                  apply False.elim assump_340
                                cases assump_339
                                case intro assump_344 assump_345 =>
                                  apply False.elim assump_344
                            case inr assump_330 =>
                              cases assump_328
                              case intro assump_350 assump_351 =>
                                apply Or.inl
                                intro assump_356
                                apply And.intro
                                cases assump_356
                                case intro assump_357 assump_358 =>
                                  apply False.elim assump_357
                                cases assump_356
                                case intro assump_361 assump_362 =>
                                  apply False.elim assump_361
                        case inr assump_322 =>
                          cases assump_318
                          case intro assump_369 assump_370 =>
                            cases assump_369
                            case inl assump_371 =>
                              cases assump_370
                              case intro assump_375 assump_376 =>
                                apply Or.inl
                                intro assump_381
                                apply And.intro
                                cases assump_381
                                case intro assump_382 assump_383 =>
                                  apply False.elim assump_382
                                cases assump_381
                                case intro assump_386 assump_387 =>
                                  apply False.elim assump_386
                            case inr assump_372 =>
                              cases assump_370
                              case intro assump_392 assump_393 =>
                                apply Or.inl
                                intro assump_398
                                apply And.intro
                                cases assump_398
                                case intro assump_399 assump_400 =>
                                  apply False.elim assump_399
                                cases assump_398
                                case intro assump_403 assump_404 =>
                                  apply False.elim assump_403
                case inr assump_310 =>
                  cases assump_310
                  case inl assump_407 =>
                    cases assump_10
                    case intro assump_411 assump_412 =>
                      cases assump_411
                      case intro assump_413 assump_414 =>
                        cases assump_413
                        case inl assump_415 =>
                          cases assump_412
                          case intro assump_421 assump_422 =>
                            cases assump_421
                            case inl assump_423 =>
                              cases assump_422
                              case intro assump_427 assump_428 =>
                                apply Or.inl
                                intro assump_433
                                apply And.intro
                                cases assump_433
                                case intro assump_434 assump_435 =>
                                  apply False.elim assump_434
                                cases assump_433
                                case intro assump_438 assump_439 =>
                                  apply False.elim assump_438
                            case inr assump_424 =>
                              cases assump_422
                              case intro assump_444 assump_445 =>
                                apply Or.inl
                                intro assump_450
                                apply And.intro
                                cases assump_450
                                case intro assump_451 assump_452 =>
                                  apply False.elim assump_451
                                cases assump_450
                                case intro assump_455 assump_456 =>
                                  apply False.elim assump_455
                        case inr assump_416 =>
                          cases assump_412
                          case intro assump_463 assump_464 =>
                            cases assump_463
                            case inl assump_465 =>
                              cases assump_464
                              case intro assump_469 assump_470 =>
                                apply Or.inl
                                intro assump_475
                                apply And.intro
                                cases assump_475
                                case intro assump_476 assump_477 =>
                                  apply False.elim assump_476
                                cases assump_475
                                case intro assump_480 assump_481 =>
                                  apply False.elim assump_480
                            case inr assump_466 =>
                              cases assump_464
                              case intro assump_486 assump_487 =>
                                apply Or.inl
                                intro assump_492
                                apply And.intro
                                cases assump_492
                                case intro assump_493 assump_494 =>
                                  apply False.elim assump_493
                                cases assump_492
                                case intro assump_497 assump_498 =>
                                  apply False.elim assump_497
                  case inr assump_408 =>
                    cases assump_10
                    case intro assump_503 assump_504 =>
                      cases assump_503
                      case intro assump_505 assump_506 =>
                        cases assump_505
                        case inl assump_507 =>
                          cases assump_504
                          case intro assump_513 assump_514 =>
                            cases assump_513
                            case inl assump_515 =>
                              cases assump_514
                              case intro assump_519 assump_520 =>
                                apply Or.inl
                                intro assump_525
                                apply And.intro
                                cases assump_525
                                case intro assump_526 assump_527 =>
                                  apply False.elim assump_526
                                cases assump_525
                                case intro assump_530 assump_531 =>
                                  apply False.elim assump_530
                            case inr assump_516 =>
                              cases assump_514
                              case intro assump_536 assump_537 =>
                                apply Or.inl
                                intro assump_542
                                apply And.intro
                                cases assump_542
                                case intro assump_543 assump_544 =>
                                  apply False.elim assump_543
                                cases assump_542
                                case intro assump_547 assump_548 =>
                                  apply False.elim assump_547
                        case inr assump_508 =>
                          cases assump_504
                          case intro assump_555 assump_556 =>
                            cases assump_555
                            case inl assump_557 =>
                              cases assump_556
                              case intro assump_561 assump_562 =>
                                apply Or.inl
                                intro assump_567
                                apply And.intro
                                cases assump_567
                                case intro assump_568 assump_569 =>
                                  apply False.elim assump_568
                                cases assump_567
                                case intro assump_572 assump_573 =>
                                  apply False.elim assump_572
                            case inr assump_558 =>
                              cases assump_556
                              case intro assump_578 assump_579 =>
                                apply Or.inl
                                intro assump_584
                                apply And.intro
                                cases assump_584
                                case intro assump_585 assump_586 =>
                                  apply False.elim assump_585
                                cases assump_584
                                case intro assump_589 assump_590 =>
                                  apply False.elim assump_589
            case inr assump_16 =>
              cases assump_14
              case inl assump_595 =>
                cases assump_12
                case inl assump_599 =>
                  cases assump_599
                  case intro assump_601 assump_602 =>
                    cases assump_10
                    case intro assump_607 assump_608 =>
                      cases assump_607
                      case intro assump_609 assump_610 =>
                        cases assump_609
                        case inl assump_611 =>
                          cases assump_608
                          case intro assump_617 assump_618 =>
                            cases assump_617
                            case inl assump_619 =>
                              cases assump_618
                              case intro assump_623 assump_624 =>
                                apply Or.inl
                                intro assump_629
                                apply And.intro
                                cases assump_629
                                case intro assump_630 assump_631 =>
                                  apply False.elim assump_630
                                cases assump_629
                                case intro assump_634 assump_635 =>
                                  apply False.elim assump_634
                            case inr assump_620 =>
                              cases assump_618
                              case intro assump_640 assump_641 =>
                                apply Or.inl
                                intro assump_646
                                apply And.intro
                                cases assump_646
                                case intro assump_647 assump_648 =>
                                  apply False.elim assump_647
                                cases assump_646
                                case intro assump_651 assump_652 =>
                                  apply False.elim assump_651
                        case inr assump_612 =>
                          cases assump_608
                          case intro assump_659 assump_660 =>
                            cases assump_659
                            case inl assump_661 =>
                              cases assump_660
                              case intro assump_665 assump_666 =>
                                apply Or.inl
                                intro assump_671
                                apply And.intro
                                cases assump_671
                                case intro assump_672 assump_673 =>
                                  apply False.elim assump_672
                                cases assump_671
                                case intro assump_676 assump_677 =>
                                  apply False.elim assump_676
                            case inr assump_662 =>
                              cases assump_660
                              case intro assump_682 assump_683 =>
                                apply Or.inl
                                intro assump_688
                                apply And.intro
                                cases assump_688
                                case intro assump_689 assump_690 =>
                                  apply False.elim assump_689
                                cases assump_688
                                case intro assump_693 assump_694 =>
                                  apply False.elim assump_693
                case inr assump_600 =>
                  cases assump_600
                  case inl assump_697 =>
                    cases assump_10
                    case intro assump_701 assump_702 =>
                      cases assump_701
                      case intro assump_703 assump_704 =>
                        cases assump_703
                        case inl assump_705 =>
                          cases assump_702
                          case intro assump_711 assump_712 =>
                            cases assump_711
                            case inl assump_713 =>
                              cases assump_712
                              case intro assump_717 assump_718 =>
                                apply Or.inl
                                intro assump_723
                                apply And.intro
                                cases assump_723
                                case intro assump_724 assump_725 =>
                                  apply False.elim assump_724
                                cases assump_723
                                case intro assump_728 assump_729 =>
                                  apply False.elim assump_728
                            case inr assump_714 =>
                              cases assump_712
                              case intro assump_734 assump_735 =>
                                apply Or.inl
                                intro assump_740
                                apply And.intro
                                cases assump_740
                                case intro assump_741 assump_742 =>
                                  apply False.elim assump_741
                                cases assump_740
                                case intro assump_745 assump_746 =>
                                  apply False.elim assump_745
                        case inr assump_706 =>
                          cases assump_702
                          case intro assump_753 assump_754 =>
                            cases assump_753
                            case inl assump_755 =>
                              cases assump_754
                              case intro assump_759 assump_760 =>
                                apply Or.inl
                                intro assump_765
                                apply And.intro
                                cases assump_765
                                case intro assump_766 assump_767 =>
                                  apply False.elim assump_766
                                cases assump_765
                                case intro assump_770 assump_771 =>
                                  apply False.elim assump_770
                            case inr assump_756 =>
                              cases assump_754
                              case intro assump_776 assump_777 =>
                                apply Or.inl
                                intro assump_782
                                apply And.intro
                                cases assump_782
                                case intro assump_783 assump_784 =>
                                  apply False.elim assump_783
                                cases assump_782
                                case intro assump_787 assump_788 =>
                                  apply False.elim assump_787
                  case inr assump_698 =>
                    cases assump_10
                    case intro assump_793 assump_794 =>
                      cases assump_793
                      case intro assump_795 assump_796 =>
                        cases assump_795
                        case inl assump_797 =>
                          cases assump_794
                          case intro assump_803 assump_804 =>
                            cases assump_803
                            case inl assump_805 =>
                              cases assump_804
                              case intro assump_809 assump_810 =>
                                apply Or.inl
                                intro assump_815
                                apply And.intro
                                cases assump_815
                                case intro assump_816 assump_817 =>
                                  apply False.elim assump_816
                                cases assump_815
                                case intro assump_820 assump_821 =>
                                  apply False.elim assump_820
                            case inr assump_806 =>
                              cases assump_804
                              case intro assump_826 assump_827 =>
                                apply Or.inl
                                intro assump_832
                                apply And.intro
                                cases assump_832
                                case intro assump_833 assump_834 =>
                                  apply False.elim assump_833
                                cases assump_832
                                case intro assump_837 assump_838 =>
                                  apply False.elim assump_837
                        case inr assump_798 =>
                          cases assump_794
                          case intro assump_845 assump_846 =>
                            cases assump_845
                            case inl assump_847 =>
                              cases assump_846
                              case intro assump_851 assump_852 =>
                                apply Or.inl
                                intro assump_857
                                apply And.intro
                                cases assump_857
                                case intro assump_858 assump_859 =>
                                  apply False.elim assump_858
                                cases assump_857
                                case intro assump_862 assump_863 =>
                                  apply False.elim assump_862
                            case inr assump_848 =>
                              cases assump_846
                              case intro assump_868 assump_869 =>
                                apply Or.inl
                                intro assump_874
                                apply And.intro
                                cases assump_874
                                case intro assump_875 assump_876 =>
                                  apply False.elim assump_875
                                cases assump_874
                                case intro assump_879 assump_880 =>
                                  apply False.elim assump_879
              case inr assump_596 =>
                cases assump_12
                case inl assump_885 =>
                  cases assump_885
                  case intro assump_887 assump_888 =>
                    cases assump_10
                    case intro assump_893 assump_894 =>
                      cases assump_893
                      case intro assump_895 assump_896 =>
                        cases assump_895
                        case inl assump_897 =>
                          cases assump_894
                          case intro assump_903 assump_904 =>
                            cases assump_903
                            case inl assump_905 =>
                              cases assump_904
                              case intro assump_909 assump_910 =>
                                apply Or.inl
                                intro assump_915
                                apply And.intro
                                cases assump_915
                                case intro assump_916 assump_917 =>
                                  apply False.elim assump_916
                                cases assump_915
                                case intro assump_920 assump_921 =>
                                  apply False.elim assump_920
                            case inr assump_906 =>
                              cases assump_904
                              case intro assump_926 assump_927 =>
                                apply Or.inl
                                intro assump_932
                                apply And.intro
                                cases assump_932
                                case intro assump_933 assump_934 =>
                                  apply False.elim assump_933
                                cases assump_932
                                case intro assump_937 assump_938 =>
                                  apply False.elim assump_937
                        case inr assump_898 =>
                          cases assump_894
                          case intro assump_945 assump_946 =>
                            cases assump_945
                            case inl assump_947 =>
                              cases assump_946
                              case intro assump_951 assump_952 =>
                                apply Or.inl
                                intro assump_957
                                apply And.intro
                                cases assump_957
                                case intro assump_958 assump_959 =>
                                  apply False.elim assump_958
                                cases assump_957
                                case intro assump_962 assump_963 =>
                                  apply False.elim assump_962
                            case inr assump_948 =>
                              cases assump_946
                              case intro assump_968 assump_969 =>
                                apply Or.inl
                                intro assump_974
                                apply And.intro
                                cases assump_974
                                case intro assump_975 assump_976 =>
                                  apply False.elim assump_975
                                cases assump_974
                                case intro assump_979 assump_980 =>
                                  apply False.elim assump_979
                case inr assump_886 =>
                  cases assump_886
                  case inl assump_983 =>
                    cases assump_10
                    case intro assump_987 assump_988 =>
                      cases assump_987
                      case intro assump_989 assump_990 =>
                        cases assump_989
                        case inl assump_991 =>
                          cases assump_988
                          case intro assump_997 assump_998 =>
                            cases assump_997
                            case inl assump_999 =>
                              cases assump_998
                              case intro assump_1003 assump_1004 =>
                                apply Or.inl
                                intro assump_1009
                                apply And.intro
                                cases assump_1009
                                case intro assump_1010 assump_1011 =>
                                  apply False.elim assump_1010
                                cases assump_1009
                                case intro assump_1014 assump_1015 =>
                                  apply False.elim assump_1014
                            case inr assump_1000 =>
                              cases assump_998
                              case intro assump_1020 assump_1021 =>
                                apply Or.inl
                                intro assump_1026
                                apply And.intro
                                cases assump_1026
                                case intro assump_1027 assump_1028 =>
                                  apply False.elim assump_1027
                                cases assump_1026
                                case intro assump_1031 assump_1032 =>
                                  apply False.elim assump_1031
                        case inr assump_992 =>
                          cases assump_988
                          case intro assump_1039 assump_1040 =>
                            cases assump_1039
                            case inl assump_1041 =>
                              cases assump_1040
                              case intro assump_1045 assump_1046 =>
                                apply Or.inl
                                intro assump_1051
                                apply And.intro
                                cases assump_1051
                                case intro assump_1052 assump_1053 =>
                                  apply False.elim assump_1052
                                cases assump_1051
                                case intro assump_1056 assump_1057 =>
                                  apply False.elim assump_1056
                            case inr assump_1042 =>
                              cases assump_1040
                              case intro assump_1062 assump_1063 =>
                                apply Or.inl
                                intro assump_1068
                                apply And.intro
                                cases assump_1068
                                case intro assump_1069 assump_1070 =>
                                  apply False.elim assump_1069
                                cases assump_1068
                                case intro assump_1073 assump_1074 =>
                                  apply False.elim assump_1073
                  case inr assump_984 =>
                    cases assump_10
                    case intro assump_1079 assump_1080 =>
                      cases assump_1079
                      case intro assump_1081 assump_1082 =>
                        cases assump_1081
                        case inl assump_1083 =>
                          cases assump_1080
                          case intro assump_1089 assump_1090 =>
                            cases assump_1089
                            case inl assump_1091 =>
                              cases assump_1090
                              case intro assump_1095 assump_1096 =>
                                apply Or.inl
                                intro assump_1101
                                apply And.intro
                                cases assump_1101
                                case intro assump_1102 assump_1103 =>
                                  apply False.elim assump_1102
                                cases assump_1101
                                case intro assump_1106 assump_1107 =>
                                  apply False.elim assump_1106
                            case inr assump_1092 =>
                              cases assump_1090
                              case intro assump_1112 assump_1113 =>
                                apply Or.inl
                                intro assump_1118
                                apply And.intro
                                cases assump_1118
                                case intro assump_1119 assump_1120 =>
                                  apply False.elim assump_1119
                                cases assump_1118
                                case intro assump_1123 assump_1124 =>
                                  apply False.elim assump_1123
                        case inr assump_1084 =>
                          cases assump_1080
                          case intro assump_1131 assump_1132 =>
                            cases assump_1131
                            case inl assump_1133 =>
                              cases assump_1132
                              case intro assump_1137 assump_1138 =>
                                apply Or.inl
                                intro assump_1143
                                apply And.intro
                                cases assump_1143
                                case intro assump_1144 assump_1145 =>
                                  apply False.elim assump_1144
                                cases assump_1143
                                case intro assump_1148 assump_1149 =>
                                  apply False.elim assump_1148
                            case inr assump_1134 =>
                              cases assump_1132
                              case intro assump_1154 assump_1155 =>
                                apply Or.inl
                                intro assump_1160
                                apply And.intro
                                cases assump_1160
                                case intro assump_1161 assump_1162 =>
                                  apply False.elim assump_1161
                                cases assump_1160
                                case intro assump_1165 assump_1166 =>
                                  apply False.elim assump_1165
    case inr assump_6 =>
      cases assump_1
      case intro assump_1171 assump_1172 =>
        cases assump_1171
        case intro assump_1173 assump_1174 =>
          cases assump_1173
          case intro assump_1175 assump_1176 =>
            cases assump_1175
            case inl assump_1177 =>
              cases assump_1176
              case inl assump_1181 =>
                cases assump_1174
                case inl assump_1185 =>
                  cases assump_1185
                  case intro assump_1187 assump_1188 =>
                    cases assump_1172
                    case intro assump_1193 assump_1194 =>
                      cases assump_1193
                      case intro assump_1195 assump_1196 =>
                        cases assump_1195
                        case inl assump_1197 =>
                          cases assump_1194
                          case intro assump_1203 assump_1204 =>
                            cases assump_1203
                            case inl assump_1205 =>
                              cases assump_1204
                              case intro assump_1209 assump_1210 =>
                                apply Or.inl
                                intro assump_1215
                                apply And.intro
                                cases assump_1215
                                case intro assump_1216 assump_1217 =>
                                  apply False.elim assump_1216
                                cases assump_1215
                                case intro assump_1220 assump_1221 =>
                                  apply False.elim assump_1220
                            case inr assump_1206 =>
                              cases assump_1204
                              case intro assump_1226 assump_1227 =>
                                apply Or.inl
                                intro assump_1232
                                apply And.intro
                                cases assump_1232
                                case intro assump_1233 assump_1234 =>
                                  apply False.elim assump_1233
                                cases assump_1232
                                case intro assump_1237 assump_1238 =>
                                  apply False.elim assump_1237
                        case inr assump_1198 =>
                          cases assump_1194
                          case intro assump_1245 assump_1246 =>
                            cases assump_1245
                            case inl assump_1247 =>
                              cases assump_1246
                              case intro assump_1251 assump_1252 =>
                                apply Or.inl
                                intro assump_1257
                                apply And.intro
                                cases assump_1257
                                case intro assump_1258 assump_1259 =>
                                  apply False.elim assump_1258
                                cases assump_1257
                                case intro assump_1262 assump_1263 =>
                                  apply False.elim assump_1262
                            case inr assump_1248 =>
                              cases assump_1246
                              case intro assump_1268 assump_1269 =>
                                apply Or.inl
                                intro assump_1274
                                apply And.intro
                                cases assump_1274
                                case intro assump_1275 assump_1276 =>
                                  apply False.elim assump_1275
                                cases assump_1274
                                case intro assump_1279 assump_1280 =>
                                  apply False.elim assump_1279
                case inr assump_1186 =>
                  cases assump_1186
                  case inl assump_1283 =>
                    cases assump_1172
                    case intro assump_1287 assump_1288 =>
                      cases assump_1287
                      case intro assump_1289 assump_1290 =>
                        cases assump_1289
                        case inl assump_1291 =>
                          cases assump_1288
                          case intro assump_1297 assump_1298 =>
                            cases assump_1297
                            case inl assump_1299 =>
                              cases assump_1298
                              case intro assump_1303 assump_1304 =>
                                apply Or.inl
                                intro assump_1309
                                apply And.intro
                                cases assump_1309
                                case intro assump_1310 assump_1311 =>
                                  apply False.elim assump_1310
                                cases assump_1309
                                case intro assump_1314 assump_1315 =>
                                  apply False.elim assump_1314
                            case inr assump_1300 =>
                              cases assump_1298
                              case intro assump_1320 assump_1321 =>
                                apply Or.inl
                                intro assump_1326
                                apply And.intro
                                cases assump_1326
                                case intro assump_1327 assump_1328 =>
                                  apply False.elim assump_1327
                                cases assump_1326
                                case intro assump_1331 assump_1332 =>
                                  apply False.elim assump_1331
                        case inr assump_1292 =>
                          cases assump_1288
                          case intro assump_1339 assump_1340 =>
                            cases assump_1339
                            case inl assump_1341 =>
                              cases assump_1340
                              case intro assump_1345 assump_1346 =>
                                apply Or.inl
                                intro assump_1351
                                apply And.intro
                                cases assump_1351
                                case intro assump_1352 assump_1353 =>
                                  apply False.elim assump_1352
                                cases assump_1351
                                case intro assump_1356 assump_1357 =>
                                  apply False.elim assump_1356
                            case inr assump_1342 =>
                              cases assump_1340
                              case intro assump_1362 assump_1363 =>
                                apply Or.inl
                                intro assump_1368
                                apply And.intro
                                cases assump_1368
                                case intro assump_1369 assump_1370 =>
                                  apply False.elim assump_1369
                                cases assump_1368
                                case intro assump_1373 assump_1374 =>
                                  apply False.elim assump_1373
                  case inr assump_1284 =>
                    cases assump_1172
                    case intro assump_1379 assump_1380 =>
                      cases assump_1379
                      case intro assump_1381 assump_1382 =>
                        cases assump_1381
                        case inl assump_1383 =>
                          cases assump_1380
                          case intro assump_1389 assump_1390 =>
                            cases assump_1389
                            case inl assump_1391 =>
                              cases assump_1390
                              case intro assump_1395 assump_1396 =>
                                apply Or.inl
                                intro assump_1401
                                apply And.intro
                                cases assump_1401
                                case intro assump_1402 assump_1403 =>
                                  apply False.elim assump_1402
                                cases assump_1401
                                case intro assump_1406 assump_1407 =>
                                  apply False.elim assump_1406
                            case inr assump_1392 =>
                              cases assump_1390
                              case intro assump_1412 assump_1413 =>
                                apply Or.inl
                                intro assump_1418
                                apply And.intro
                                cases assump_1418
                                case intro assump_1419 assump_1420 =>
                                  apply False.elim assump_1419
                                cases assump_1418
                                case intro assump_1423 assump_1424 =>
                                  apply False.elim assump_1423
                        case inr assump_1384 =>
                          cases assump_1380
                          case intro assump_1431 assump_1432 =>
                            cases assump_1431
                            case inl assump_1433 =>
                              cases assump_1432
                              case intro assump_1437 assump_1438 =>
                                apply Or.inl
                                intro assump_1443
                                apply And.intro
                                cases assump_1443
                                case intro assump_1444 assump_1445 =>
                                  apply False.elim assump_1444
                                cases assump_1443
                                case intro assump_1448 assump_1449 =>
                                  apply False.elim assump_1448
                            case inr assump_1434 =>
                              cases assump_1432
                              case intro assump_1454 assump_1455 =>
                                apply Or.inl
                                intro assump_1460
                                apply And.intro
                                cases assump_1460
                                case intro assump_1461 assump_1462 =>
                                  apply False.elim assump_1461
                                cases assump_1460
                                case intro assump_1465 assump_1466 =>
                                  apply False.elim assump_1465
              case inr assump_1182 =>
                cases assump_1174
                case inl assump_1471 =>
                  cases assump_1471
                  case intro assump_1473 assump_1474 =>
                    cases assump_1172
                    case intro assump_1479 assump_1480 =>
                      cases assump_1479
                      case intro assump_1481 assump_1482 =>
                        cases assump_1481
                        case inl assump_1483 =>
                          cases assump_1480
                          case intro assump_1489 assump_1490 =>
                            cases assump_1489
                            case inl assump_1491 =>
                              cases assump_1490
                              case intro assump_1495 assump_1496 =>
                                apply Or.inl
                                intro assump_1501
                                apply And.intro
                                cases assump_1501
                                case intro assump_1502 assump_1503 =>
                                  apply False.elim assump_1502
                                cases assump_1501
                                case intro assump_1506 assump_1507 =>
                                  apply False.elim assump_1506
                            case inr assump_1492 =>
                              cases assump_1490
                              case intro assump_1512 assump_1513 =>
                                apply Or.inl
                                intro assump_1518
                                apply And.intro
                                cases assump_1518
                                case intro assump_1519 assump_1520 =>
                                  apply False.elim assump_1519
                                cases assump_1518
                                case intro assump_1523 assump_1524 =>
                                  apply False.elim assump_1523
                        case inr assump_1484 =>
                          cases assump_1480
                          case intro assump_1531 assump_1532 =>
                            cases assump_1531
                            case inl assump_1533 =>
                              cases assump_1532
                              case intro assump_1537 assump_1538 =>
                                apply Or.inl
                                intro assump_1543
                                apply And.intro
                                cases assump_1543
                                case intro assump_1544 assump_1545 =>
                                  apply False.elim assump_1544
                                cases assump_1543
                                case intro assump_1548 assump_1549 =>
                                  apply False.elim assump_1548
                            case inr assump_1534 =>
                              cases assump_1532
                              case intro assump_1554 assump_1555 =>
                                apply Or.inl
                                intro assump_1560
                                apply And.intro
                                cases assump_1560
                                case intro assump_1561 assump_1562 =>
                                  apply False.elim assump_1561
                                cases assump_1560
                                case intro assump_1565 assump_1566 =>
                                  apply False.elim assump_1565
                case inr assump_1472 =>
                  cases assump_1472
                  case inl assump_1569 =>
                    cases assump_1172
                    case intro assump_1573 assump_1574 =>
                      cases assump_1573
                      case intro assump_1575 assump_1576 =>
                        cases assump_1575
                        case inl assump_1577 =>
                          cases assump_1574
                          case intro assump_1583 assump_1584 =>
                            cases assump_1583
                            case inl assump_1585 =>
                              cases assump_1584
                              case intro assump_1589 assump_1590 =>
                                apply Or.inl
                                intro assump_1595
                                apply And.intro
                                cases assump_1595
                                case intro assump_1596 assump_1597 =>
                                  apply False.elim assump_1596
                                cases assump_1595
                                case intro assump_1600 assump_1601 =>
                                  apply False.elim assump_1600
                            case inr assump_1586 =>
                              cases assump_1584
                              case intro assump_1606 assump_1607 =>
                                apply Or.inl
                                intro assump_1612
                                apply And.intro
                                cases assump_1612
                                case intro assump_1613 assump_1614 =>
                                  apply False.elim assump_1613
                                cases assump_1612
                                case intro assump_1617 assump_1618 =>
                                  apply False.elim assump_1617
                        case inr assump_1578 =>
                          cases assump_1574
                          case intro assump_1625 assump_1626 =>
                            cases assump_1625
                            case inl assump_1627 =>
                              cases assump_1626
                              case intro assump_1631 assump_1632 =>
                                apply Or.inl
                                intro assump_1637
                                apply And.intro
                                cases assump_1637
                                case intro assump_1638 assump_1639 =>
                                  apply False.elim assump_1638
                                cases assump_1637
                                case intro assump_1642 assump_1643 =>
                                  apply False.elim assump_1642
                            case inr assump_1628 =>
                              cases assump_1626
                              case intro assump_1648 assump_1649 =>
                                apply Or.inl
                                intro assump_1654
                                apply And.intro
                                cases assump_1654
                                case intro assump_1655 assump_1656 =>
                                  apply False.elim assump_1655
                                cases assump_1654
                                case intro assump_1659 assump_1660 =>
                                  apply False.elim assump_1659
                  case inr assump_1570 =>
                    cases assump_1172
                    case intro assump_1665 assump_1666 =>
                      cases assump_1665
                      case intro assump_1667 assump_1668 =>
                        cases assump_1667
                        case inl assump_1669 =>
                          cases assump_1666
                          case intro assump_1675 assump_1676 =>
                            cases assump_1675
                            case inl assump_1677 =>
                              cases assump_1676
                              case intro assump_1681 assump_1682 =>
                                apply Or.inl
                                intro assump_1687
                                apply And.intro
                                cases assump_1687
                                case intro assump_1688 assump_1689 =>
                                  apply False.elim assump_1688
                                cases assump_1687
                                case intro assump_1692 assump_1693 =>
                                  apply False.elim assump_1692
                            case inr assump_1678 =>
                              cases assump_1676
                              case intro assump_1698 assump_1699 =>
                                apply Or.inl
                                intro assump_1704
                                apply And.intro
                                cases assump_1704
                                case intro assump_1705 assump_1706 =>
                                  apply False.elim assump_1705
                                cases assump_1704
                                case intro assump_1709 assump_1710 =>
                                  apply False.elim assump_1709
                        case inr assump_1670 =>
                          cases assump_1666
                          case intro assump_1717 assump_1718 =>
                            cases assump_1717
                            case inl assump_1719 =>
                              cases assump_1718
                              case intro assump_1723 assump_1724 =>
                                apply Or.inl
                                intro assump_1729
                                apply And.intro
                                cases assump_1729
                                case intro assump_1730 assump_1731 =>
                                  apply False.elim assump_1730
                                cases assump_1729
                                case intro assump_1734 assump_1735 =>
                                  apply False.elim assump_1734
                            case inr assump_1720 =>
                              cases assump_1718
                              case intro assump_1740 assump_1741 =>
                                apply Or.inl
                                intro assump_1746
                                apply And.intro
                                cases assump_1746
                                case intro assump_1747 assump_1748 =>
                                  apply False.elim assump_1747
                                cases assump_1746
                                case intro assump_1751 assump_1752 =>
                                  apply False.elim assump_1751
            case inr assump_1178 =>
              cases assump_1176
              case inl assump_1757 =>
                cases assump_1174
                case inl assump_1761 =>
                  cases assump_1761
                  case intro assump_1763 assump_1764 =>
                    cases assump_1172
                    case intro assump_1769 assump_1770 =>
                      cases assump_1769
                      case intro assump_1771 assump_1772 =>
                        cases assump_1771
                        case inl assump_1773 =>
                          cases assump_1770
                          case intro assump_1779 assump_1780 =>
                            cases assump_1779
                            case inl assump_1781 =>
                              cases assump_1780
                              case intro assump_1785 assump_1786 =>
                                apply Or.inl
                                intro assump_1791
                                apply And.intro
                                cases assump_1791
                                case intro assump_1792 assump_1793 =>
                                  apply False.elim assump_1792
                                cases assump_1791
                                case intro assump_1796 assump_1797 =>
                                  apply False.elim assump_1796
                            case inr assump_1782 =>
                              cases assump_1780
                              case intro assump_1802 assump_1803 =>
                                apply Or.inl
                                intro assump_1808
                                apply And.intro
                                cases assump_1808
                                case intro assump_1809 assump_1810 =>
                                  apply False.elim assump_1809
                                cases assump_1808
                                case intro assump_1813 assump_1814 =>
                                  apply False.elim assump_1813
                        case inr assump_1774 =>
                          cases assump_1770
                          case intro assump_1821 assump_1822 =>
                            cases assump_1821
                            case inl assump_1823 =>
                              cases assump_1822
                              case intro assump_1827 assump_1828 =>
                                apply Or.inl
                                intro assump_1833
                                apply And.intro
                                cases assump_1833
                                case intro assump_1834 assump_1835 =>
                                  apply False.elim assump_1834
                                cases assump_1833
                                case intro assump_1838 assump_1839 =>
                                  apply False.elim assump_1838
                            case inr assump_1824 =>
                              cases assump_1822
                              case intro assump_1844 assump_1845 =>
                                apply Or.inl
                                intro assump_1850
                                apply And.intro
                                cases assump_1850
                                case intro assump_1851 assump_1852 =>
                                  apply False.elim assump_1851
                                cases assump_1850
                                case intro assump_1855 assump_1856 =>
                                  apply False.elim assump_1855
                case inr assump_1762 =>
                  cases assump_1762
                  case inl assump_1859 =>
                    cases assump_1172
                    case intro assump_1863 assump_1864 =>
                      cases assump_1863
                      case intro assump_1865 assump_1866 =>
                        cases assump_1865
                        case inl assump_1867 =>
                          cases assump_1864
                          case intro assump_1873 assump_1874 =>
                            cases assump_1873
                            case inl assump_1875 =>
                              cases assump_1874
                              case intro assump_1879 assump_1880 =>
                                apply Or.inl
                                intro assump_1885
                                apply And.intro
                                cases assump_1885
                                case intro assump_1886 assump_1887 =>
                                  apply False.elim assump_1886
                                cases assump_1885
                                case intro assump_1890 assump_1891 =>
                                  apply False.elim assump_1890
                            case inr assump_1876 =>
                              cases assump_1874
                              case intro assump_1896 assump_1897 =>
                                apply Or.inl
                                intro assump_1902
                                apply And.intro
                                cases assump_1902
                                case intro assump_1903 assump_1904 =>
                                  apply False.elim assump_1903
                                cases assump_1902
                                case intro assump_1907 assump_1908 =>
                                  apply False.elim assump_1907
                        case inr assump_1868 =>
                          cases assump_1864
                          case intro assump_1915 assump_1916 =>
                            cases assump_1915
                            case inl assump_1917 =>
                              cases assump_1916
                              case intro assump_1921 assump_1922 =>
                                apply Or.inl
                                intro assump_1927
                                apply And.intro
                                cases assump_1927
                                case intro assump_1928 assump_1929 =>
                                  apply False.elim assump_1928
                                cases assump_1927
                                case intro assump_1932 assump_1933 =>
                                  apply False.elim assump_1932
                            case inr assump_1918 =>
                              cases assump_1916
                              case intro assump_1938 assump_1939 =>
                                apply Or.inl
                                intro assump_1944
                                apply And.intro
                                cases assump_1944
                                case intro assump_1945 assump_1946 =>
                                  apply False.elim assump_1945
                                cases assump_1944
                                case intro assump_1949 assump_1950 =>
                                  apply False.elim assump_1949
                  case inr assump_1860 =>
                    cases assump_1172
                    case intro assump_1955 assump_1956 =>
                      cases assump_1955
                      case intro assump_1957 assump_1958 =>
                        cases assump_1957
                        case inl assump_1959 =>
                          cases assump_1956
                          case intro assump_1965 assump_1966 =>
                            cases assump_1965
                            case inl assump_1967 =>
                              cases assump_1966
                              case intro assump_1971 assump_1972 =>
                                apply Or.inl
                                intro assump_1977
                                apply And.intro
                                cases assump_1977
                                case intro assump_1978 assump_1979 =>
                                  apply False.elim assump_1978
                                cases assump_1977
                                case intro assump_1982 assump_1983 =>
                                  apply False.elim assump_1982
                            case inr assump_1968 =>
                              cases assump_1966
                              case intro assump_1988 assump_1989 =>
                                apply Or.inl
                                intro assump_1994
                                apply And.intro
                                cases assump_1994
                                case intro assump_1995 assump_1996 =>
                                  apply False.elim assump_1995
                                cases assump_1994
                                case intro assump_1999 assump_2000 =>
                                  apply False.elim assump_1999
                        case inr assump_1960 =>
                          cases assump_1956
                          case intro assump_2007 assump_2008 =>
                            cases assump_2007
                            case inl assump_2009 =>
                              cases assump_2008
                              case intro assump_2013 assump_2014 =>
                                apply Or.inl
                                intro assump_2019
                                apply And.intro
                                cases assump_2019
                                case intro assump_2020 assump_2021 =>
                                  apply False.elim assump_2020
                                cases assump_2019
                                case intro assump_2024 assump_2025 =>
                                  apply False.elim assump_2024
                            case inr assump_2010 =>
                              cases assump_2008
                              case intro assump_2030 assump_2031 =>
                                apply Or.inl
                                intro assump_2036
                                apply And.intro
                                cases assump_2036
                                case intro assump_2037 assump_2038 =>
                                  apply False.elim assump_2037
                                cases assump_2036
                                case intro assump_2041 assump_2042 =>
                                  apply False.elim assump_2041
              case inr assump_1758 =>
                cases assump_1174
                case inl assump_2047 =>
                  cases assump_2047
                  case intro assump_2049 assump_2050 =>
                    cases assump_1172
                    case intro assump_2055 assump_2056 =>
                      cases assump_2055
                      case intro assump_2057 assump_2058 =>
                        cases assump_2057
                        case inl assump_2059 =>
                          cases assump_2056
                          case intro assump_2065 assump_2066 =>
                            cases assump_2065
                            case inl assump_2067 =>
                              cases assump_2066
                              case intro assump_2071 assump_2072 =>
                                apply Or.inl
                                intro assump_2077
                                apply And.intro
                                cases assump_2077
                                case intro assump_2078 assump_2079 =>
                                  apply False.elim assump_2078
                                cases assump_2077
                                case intro assump_2082 assump_2083 =>
                                  apply False.elim assump_2082
                            case inr assump_2068 =>
                              cases assump_2066
                              case intro assump_2088 assump_2089 =>
                                apply Or.inl
                                intro assump_2094
                                apply And.intro
                                cases assump_2094
                                case intro assump_2095 assump_2096 =>
                                  apply False.elim assump_2095
                                cases assump_2094
                                case intro assump_2099 assump_2100 =>
                                  apply False.elim assump_2099
                        case inr assump_2060 =>
                          cases assump_2056
                          case intro assump_2107 assump_2108 =>
                            cases assump_2107
                            case inl assump_2109 =>
                              cases assump_2108
                              case intro assump_2113 assump_2114 =>
                                apply Or.inl
                                intro assump_2119
                                apply And.intro
                                cases assump_2119
                                case intro assump_2120 assump_2121 =>
                                  apply False.elim assump_2120
                                cases assump_2119
                                case intro assump_2124 assump_2125 =>
                                  apply False.elim assump_2124
                            case inr assump_2110 =>
                              cases assump_2108
                              case intro assump_2130 assump_2131 =>
                                apply Or.inl
                                intro assump_2136
                                apply And.intro
                                cases assump_2136
                                case intro assump_2137 assump_2138 =>
                                  apply False.elim assump_2137
                                cases assump_2136
                                case intro assump_2141 assump_2142 =>
                                  apply False.elim assump_2141
                case inr assump_2048 =>
                  cases assump_2048
                  case inl assump_2145 =>
                    cases assump_1172
                    case intro assump_2149 assump_2150 =>
                      cases assump_2149
                      case intro assump_2151 assump_2152 =>
                        cases assump_2151
                        case inl assump_2153 =>
                          cases assump_2150
                          case intro assump_2159 assump_2160 =>
                            cases assump_2159
                            case inl assump_2161 =>
                              cases assump_2160
                              case intro assump_2165 assump_2166 =>
                                apply Or.inl
                                intro assump_2171
                                apply And.intro
                                cases assump_2171
                                case intro assump_2172 assump_2173 =>
                                  apply False.elim assump_2172
                                cases assump_2171
                                case intro assump_2176 assump_2177 =>
                                  apply False.elim assump_2176
                            case inr assump_2162 =>
                              cases assump_2160
                              case intro assump_2182 assump_2183 =>
                                apply Or.inl
                                intro assump_2188
                                apply And.intro
                                cases assump_2188
                                case intro assump_2189 assump_2190 =>
                                  apply False.elim assump_2189
                                cases assump_2188
                                case intro assump_2193 assump_2194 =>
                                  apply False.elim assump_2193
                        case inr assump_2154 =>
                          cases assump_2150
                          case intro assump_2201 assump_2202 =>
                            cases assump_2201
                            case inl assump_2203 =>
                              cases assump_2202
                              case intro assump_2207 assump_2208 =>
                                apply Or.inl
                                intro assump_2213
                                apply And.intro
                                cases assump_2213
                                case intro assump_2214 assump_2215 =>
                                  apply False.elim assump_2214
                                cases assump_2213
                                case intro assump_2218 assump_2219 =>
                                  apply False.elim assump_2218
                            case inr assump_2204 =>
                              cases assump_2202
                              case intro assump_2224 assump_2225 =>
                                apply Or.inl
                                intro assump_2230
                                apply And.intro
                                cases assump_2230
                                case intro assump_2231 assump_2232 =>
                                  apply False.elim assump_2231
                                cases assump_2230
                                case intro assump_2235 assump_2236 =>
                                  apply False.elim assump_2235
                  case inr assump_2146 =>
                    cases assump_1172
                    case intro assump_2241 assump_2242 =>
                      cases assump_2241
                      case intro assump_2243 assump_2244 =>
                        cases assump_2243
                        case inl assump_2245 =>
                          cases assump_2242
                          case intro assump_2251 assump_2252 =>
                            cases assump_2251
                            case inl assump_2253 =>
                              cases assump_2252
                              case intro assump_2257 assump_2258 =>
                                apply Or.inl
                                intro assump_2263
                                apply And.intro
                                cases assump_2263
                                case intro assump_2264 assump_2265 =>
                                  apply False.elim assump_2264
                                cases assump_2263
                                case intro assump_2268 assump_2269 =>
                                  apply False.elim assump_2268
                            case inr assump_2254 =>
                              cases assump_2252
                              case intro assump_2274 assump_2275 =>
                                apply Or.inl
                                intro assump_2280
                                apply And.intro
                                cases assump_2280
                                case intro assump_2281 assump_2282 =>
                                  apply False.elim assump_2281
                                cases assump_2280
                                case intro assump_2285 assump_2286 =>
                                  apply False.elim assump_2285
                        case inr assump_2246 =>
                          cases assump_2242
                          case intro assump_2293 assump_2294 =>
                            cases assump_2293
                            case inl assump_2295 =>
                              cases assump_2294
                              case intro assump_2299 assump_2300 =>
                                apply Or.inl
                                intro assump_2305
                                apply And.intro
                                cases assump_2305
                                case intro assump_2306 assump_2307 =>
                                  apply False.elim assump_2306
                                cases assump_2305
                                case intro assump_2310 assump_2311 =>
                                  apply False.elim assump_2310
                            case inr assump_2296 =>
                              cases assump_2294
                              case intro assump_2316 assump_2317 =>
                                apply Or.inl
                                intro assump_2322
                                apply And.intro
                                cases assump_2322
                                case intro assump_2323 assump_2324 =>
                                  apply False.elim assump_2323
                                cases assump_2322
                                case intro assump_2327 assump_2328 =>
                                  apply False.elim assump_2327
  case inr assump_4 =>
    cases assump_4
    case inl assump_2331 =>
      cases assump_2331
      case intro assump_2333 assump_2334 =>
        apply False.elim assump_2334
    case inr assump_2332 =>
      cases assump_2332
      case intro assump_2339 assump_2340 =>
        cases assump_1
        case intro assump_2345 assump_2346 =>
          cases assump_2345
          case intro assump_2347 assump_2348 =>
            cases assump_2347
            case intro assump_2349 assump_2350 =>
              cases assump_2349
              case inl assump_2351 =>
                cases assump_2350
                case inl assump_2355 =>
                  cases assump_2348
                  case inl assump_2359 =>
                    cases assump_2359
                    case intro assump_2361 assump_2362 =>
                      cases assump_2346
                      case intro assump_2367 assump_2368 =>
                        cases assump_2367
                        case intro assump_2369 assump_2370 =>
                          cases assump_2369
                          case inl assump_2371 =>
                            cases assump_2368
                            case intro assump_2377 assump_2378 =>
                              cases assump_2377
                              case inl assump_2379 =>
                                cases assump_2378
                                case intro assump_2383 assump_2384 =>
                                  apply Or.inl
                                  intro assump_2389
                                  apply And.intro
                                  cases assump_2389
                                  case intro assump_2390 assump_2391 =>
                                    apply False.elim assump_2390
                                  cases assump_2389
                                  case intro assump_2394 assump_2395 =>
                                    apply False.elim assump_2394
                              case inr assump_2380 =>
                                cases assump_2378
                                case intro assump_2400 assump_2401 =>
                                  apply Or.inl
                                  intro assump_2406
                                  apply And.intro
                                  cases assump_2406
                                  case intro assump_2407 assump_2408 =>
                                    apply False.elim assump_2407
                                  cases assump_2406
                                  case intro assump_2411 assump_2412 =>
                                    apply False.elim assump_2411
                          case inr assump_2372 =>
                            cases assump_2368
                            case intro assump_2419 assump_2420 =>
                              cases assump_2419
                              case inl assump_2421 =>
                                cases assump_2420
                                case intro assump_2425 assump_2426 =>
                                  apply Or.inl
                                  intro assump_2431
                                  apply And.intro
                                  cases assump_2431
                                  case intro assump_2432 assump_2433 =>
                                    apply False.elim assump_2432
                                  cases assump_2431
                                  case intro assump_2436 assump_2437 =>
                                    apply False.elim assump_2436
                              case inr assump_2422 =>
                                cases assump_2420
                                case intro assump_2442 assump_2443 =>
                                  apply Or.inl
                                  intro assump_2448
                                  apply And.intro
                                  cases assump_2448
                                  case intro assump_2449 assump_2450 =>
                                    apply False.elim assump_2449
                                  cases assump_2448
                                  case intro assump_2453 assump_2454 =>
                                    apply False.elim assump_2453
                  case inr assump_2360 =>
                    cases assump_2360
                    case inl assump_2457 =>
                      cases assump_2346
                      case intro assump_2461 assump_2462 =>
                        cases assump_2461
                        case intro assump_2463 assump_2464 =>
                          cases assump_2463
                          case inl assump_2465 =>
                            cases assump_2462
                            case intro assump_2471 assump_2472 =>
                              cases assump_2471
                              case inl assump_2473 =>
                                cases assump_2472
                                case intro assump_2477 assump_2478 =>
                                  apply Or.inl
                                  intro assump_2483
                                  apply And.intro
                                  cases assump_2483
                                  case intro assump_2484 assump_2485 =>
                                    apply False.elim assump_2484
                                  cases assump_2483
                                  case intro assump_2488 assump_2489 =>
                                    apply False.elim assump_2488
                              case inr assump_2474 =>
                                cases assump_2472
                                case intro assump_2494 assump_2495 =>
                                  apply Or.inl
                                  intro assump_2500
                                  apply And.intro
                                  cases assump_2500
                                  case intro assump_2501 assump_2502 =>
                                    apply False.elim assump_2501
                                  cases assump_2500
                                  case intro assump_2505 assump_2506 =>
                                    apply False.elim assump_2505
                          case inr assump_2466 =>
                            cases assump_2462
                            case intro assump_2513 assump_2514 =>
                              cases assump_2513
                              case inl assump_2515 =>
                                cases assump_2514
                                case intro assump_2519 assump_2520 =>
                                  apply Or.inl
                                  intro assump_2525
                                  apply And.intro
                                  cases assump_2525
                                  case intro assump_2526 assump_2527 =>
                                    apply False.elim assump_2526
                                  cases assump_2525
                                  case intro assump_2530 assump_2531 =>
                                    apply False.elim assump_2530
                              case inr assump_2516 =>
                                cases assump_2514
                                case intro assump_2536 assump_2537 =>
                                  apply Or.inl
                                  intro assump_2542
                                  apply And.intro
                                  cases assump_2542
                                  case intro assump_2543 assump_2544 =>
                                    apply False.elim assump_2543
                                  cases assump_2542
                                  case intro assump_2547 assump_2548 =>
                                    apply False.elim assump_2547
                    case inr assump_2458 =>
                      cases assump_2346
                      case intro assump_2553 assump_2554 =>
                        cases assump_2553
                        case intro assump_2555 assump_2556 =>
                          cases assump_2555
                          case inl assump_2557 =>
                            cases assump_2554
                            case intro assump_2563 assump_2564 =>
                              cases assump_2563
                              case inl assump_2565 =>
                                cases assump_2564
                                case intro assump_2569 assump_2570 =>
                                  apply Or.inl
                                  intro assump_2575
                                  apply And.intro
                                  cases assump_2575
                                  case intro assump_2576 assump_2577 =>
                                    apply False.elim assump_2576
                                  cases assump_2575
                                  case intro assump_2580 assump_2581 =>
                                    apply False.elim assump_2580
                              case inr assump_2566 =>
                                cases assump_2564
                                case intro assump_2586 assump_2587 =>
                                  apply Or.inl
                                  intro assump_2592
                                  apply And.intro
                                  cases assump_2592
                                  case intro assump_2593 assump_2594 =>
                                    apply False.elim assump_2593
                                  cases assump_2592
                                  case intro assump_2597 assump_2598 =>
                                    apply False.elim assump_2597
                          case inr assump_2558 =>
                            cases assump_2554
                            case intro assump_2605 assump_2606 =>
                              cases assump_2605
                              case inl assump_2607 =>
                                cases assump_2606
                                case intro assump_2611 assump_2612 =>
                                  apply Or.inl
                                  intro assump_2617
                                  apply And.intro
                                  cases assump_2617
                                  case intro assump_2618 assump_2619 =>
                                    apply False.elim assump_2618
                                  cases assump_2617
                                  case intro assump_2622 assump_2623 =>
                                    apply False.elim assump_2622
                              case inr assump_2608 =>
                                cases assump_2606
                                case intro assump_2628 assump_2629 =>
                                  apply Or.inl
                                  intro assump_2634
                                  apply And.intro
                                  cases assump_2634
                                  case intro assump_2635 assump_2636 =>
                                    apply False.elim assump_2635
                                  cases assump_2634
                                  case intro assump_2639 assump_2640 =>
                                    apply False.elim assump_2639
                case inr assump_2356 =>
                  cases assump_2348
                  case inl assump_2645 =>
                    cases assump_2645
                    case intro assump_2647 assump_2648 =>
                      cases assump_2346
                      case intro assump_2653 assump_2654 =>
                        cases assump_2653
                        case intro assump_2655 assump_2656 =>
                          cases assump_2655
                          case inl assump_2657 =>
                            cases assump_2654
                            case intro assump_2663 assump_2664 =>
                              cases assump_2663
                              case inl assump_2665 =>
                                cases assump_2664
                                case intro assump_2669 assump_2670 =>
                                  apply Or.inl
                                  intro assump_2675
                                  apply And.intro
                                  cases assump_2675
                                  case intro assump_2676 assump_2677 =>
                                    apply False.elim assump_2676
                                  cases assump_2675
                                  case intro assump_2680 assump_2681 =>
                                    apply False.elim assump_2680
                              case inr assump_2666 =>
                                cases assump_2664
                                case intro assump_2686 assump_2687 =>
                                  apply Or.inl
                                  intro assump_2692
                                  apply And.intro
                                  cases assump_2692
                                  case intro assump_2693 assump_2694 =>
                                    apply False.elim assump_2693
                                  cases assump_2692
                                  case intro assump_2697 assump_2698 =>
                                    apply False.elim assump_2697
                          case inr assump_2658 =>
                            cases assump_2654
                            case intro assump_2705 assump_2706 =>
                              cases assump_2705
                              case inl assump_2707 =>
                                cases assump_2706
                                case intro assump_2711 assump_2712 =>
                                  apply Or.inl
                                  intro assump_2717
                                  apply And.intro
                                  cases assump_2717
                                  case intro assump_2718 assump_2719 =>
                                    apply False.elim assump_2718
                                  cases assump_2717
                                  case intro assump_2722 assump_2723 =>
                                    apply False.elim assump_2722
                              case inr assump_2708 =>
                                cases assump_2706
                                case intro assump_2728 assump_2729 =>
                                  apply Or.inl
                                  intro assump_2734
                                  apply And.intro
                                  cases assump_2734
                                  case intro assump_2735 assump_2736 =>
                                    apply False.elim assump_2735
                                  cases assump_2734
                                  case intro assump_2739 assump_2740 =>
                                    apply False.elim assump_2739
                  case inr assump_2646 =>
                    cases assump_2646
                    case inl assump_2743 =>
                      cases assump_2346
                      case intro assump_2747 assump_2748 =>
                        cases assump_2747
                        case intro assump_2749 assump_2750 =>
                          cases assump_2749
                          case inl assump_2751 =>
                            cases assump_2748
                            case intro assump_2757 assump_2758 =>
                              cases assump_2757
                              case inl assump_2759 =>
                                cases assump_2758
                                case intro assump_2763 assump_2764 =>
                                  apply Or.inl
                                  intro assump_2769
                                  apply And.intro
                                  cases assump_2769
                                  case intro assump_2770 assump_2771 =>
                                    apply False.elim assump_2770
                                  cases assump_2769
                                  case intro assump_2774 assump_2775 =>
                                    apply False.elim assump_2774
                              case inr assump_2760 =>
                                cases assump_2758
                                case intro assump_2780 assump_2781 =>
                                  apply Or.inl
                                  intro assump_2786
                                  apply And.intro
                                  cases assump_2786
                                  case intro assump_2787 assump_2788 =>
                                    apply False.elim assump_2787
                                  cases assump_2786
                                  case intro assump_2791 assump_2792 =>
                                    apply False.elim assump_2791
                          case inr assump_2752 =>
                            cases assump_2748
                            case intro assump_2799 assump_2800 =>
                              cases assump_2799
                              case inl assump_2801 =>
                                cases assump_2800
                                case intro assump_2805 assump_2806 =>
                                  apply Or.inl
                                  intro assump_2811
                                  apply And.intro
                                  cases assump_2811
                                  case intro assump_2812 assump_2813 =>
                                    apply False.elim assump_2812
                                  cases assump_2811
                                  case intro assump_2816 assump_2817 =>
                                    apply False.elim assump_2816
                              case inr assump_2802 =>
                                cases assump_2800
                                case intro assump_2822 assump_2823 =>
                                  apply Or.inl
                                  intro assump_2828
                                  apply And.intro
                                  cases assump_2828
                                  case intro assump_2829 assump_2830 =>
                                    apply False.elim assump_2829
                                  cases assump_2828
                                  case intro assump_2833 assump_2834 =>
                                    apply False.elim assump_2833
                    case inr assump_2744 =>
                      cases assump_2346
                      case intro assump_2839 assump_2840 =>
                        cases assump_2839
                        case intro assump_2841 assump_2842 =>
                          cases assump_2841
                          case inl assump_2843 =>
                            cases assump_2840
                            case intro assump_2849 assump_2850 =>
                              cases assump_2849
                              case inl assump_2851 =>
                                cases assump_2850
                                case intro assump_2855 assump_2856 =>
                                  apply Or.inl
                                  intro assump_2861
                                  apply And.intro
                                  cases assump_2861
                                  case intro assump_2862 assump_2863 =>
                                    apply False.elim assump_2862
                                  cases assump_2861
                                  case intro assump_2866 assump_2867 =>
                                    apply False.elim assump_2866
                              case inr assump_2852 =>
                                cases assump_2850
                                case intro assump_2872 assump_2873 =>
                                  apply Or.inl
                                  intro assump_2878
                                  apply And.intro
                                  cases assump_2878
                                  case intro assump_2879 assump_2880 =>
                                    apply False.elim assump_2879
                                  cases assump_2878
                                  case intro assump_2883 assump_2884 =>
                                    apply False.elim assump_2883
                          case inr assump_2844 =>
                            cases assump_2840
                            case intro assump_2891 assump_2892 =>
                              cases assump_2891
                              case inl assump_2893 =>
                                cases assump_2892
                                case intro assump_2897 assump_2898 =>
                                  apply Or.inl
                                  intro assump_2903
                                  apply And.intro
                                  cases assump_2903
                                  case intro assump_2904 assump_2905 =>
                                    apply False.elim assump_2904
                                  cases assump_2903
                                  case intro assump_2908 assump_2909 =>
                                    apply False.elim assump_2908
                              case inr assump_2894 =>
                                cases assump_2892
                                case intro assump_2914 assump_2915 =>
                                  apply Or.inl
                                  intro assump_2920
                                  apply And.intro
                                  cases assump_2920
                                  case intro assump_2921 assump_2922 =>
                                    apply False.elim assump_2921
                                  cases assump_2920
                                  case intro assump_2925 assump_2926 =>
                                    apply False.elim assump_2925
              case inr assump_2352 =>
                cases assump_2350
                case inl assump_2931 =>
                  cases assump_2348
                  case inl assump_2935 =>
                    cases assump_2935
                    case intro assump_2937 assump_2938 =>
                      cases assump_2346
                      case intro assump_2943 assump_2944 =>
                        cases assump_2943
                        case intro assump_2945 assump_2946 =>
                          cases assump_2945
                          case inl assump_2947 =>
                            cases assump_2944
                            case intro assump_2953 assump_2954 =>
                              cases assump_2953
                              case inl assump_2955 =>
                                cases assump_2954
                                case intro assump_2959 assump_2960 =>
                                  apply Or.inl
                                  intro assump_2965
                                  apply And.intro
                                  cases assump_2965
                                  case intro assump_2966 assump_2967 =>
                                    apply False.elim assump_2966
                                  cases assump_2965
                                  case intro assump_2970 assump_2971 =>
                                    apply False.elim assump_2970
                              case inr assump_2956 =>
                                cases assump_2954
                                case intro assump_2976 assump_2977 =>
                                  apply Or.inl
                                  intro assump_2982
                                  apply And.intro
                                  cases assump_2982
                                  case intro assump_2983 assump_2984 =>
                                    apply False.elim assump_2983
                                  cases assump_2982
                                  case intro assump_2987 assump_2988 =>
                                    apply False.elim assump_2987
                          case inr assump_2948 =>
                            cases assump_2944
                            case intro assump_2995 assump_2996 =>
                              cases assump_2995
                              case inl assump_2997 =>
                                cases assump_2996
                                case intro assump_3001 assump_3002 =>
                                  apply Or.inl
                                  intro assump_3007
                                  apply And.intro
                                  cases assump_3007
                                  case intro assump_3008 assump_3009 =>
                                    apply False.elim assump_3008
                                  cases assump_3007
                                  case intro assump_3012 assump_3013 =>
                                    apply False.elim assump_3012
                              case inr assump_2998 =>
                                cases assump_2996
                                case intro assump_3018 assump_3019 =>
                                  apply Or.inl
                                  intro assump_3024
                                  apply And.intro
                                  cases assump_3024
                                  case intro assump_3025 assump_3026 =>
                                    apply False.elim assump_3025
                                  cases assump_3024
                                  case intro assump_3029 assump_3030 =>
                                    apply False.elim assump_3029
                  case inr assump_2936 =>
                    cases assump_2936
                    case inl assump_3033 =>
                      cases assump_2346
                      case intro assump_3037 assump_3038 =>
                        cases assump_3037
                        case intro assump_3039 assump_3040 =>
                          cases assump_3039
                          case inl assump_3041 =>
                            cases assump_3038
                            case intro assump_3047 assump_3048 =>
                              cases assump_3047
                              case inl assump_3049 =>
                                cases assump_3048
                                case intro assump_3053 assump_3054 =>
                                  apply Or.inl
                                  intro assump_3059
                                  apply And.intro
                                  cases assump_3059
                                  case intro assump_3060 assump_3061 =>
                                    apply False.elim assump_3060
                                  cases assump_3059
                                  case intro assump_3064 assump_3065 =>
                                    apply False.elim assump_3064
                              case inr assump_3050 =>
                                cases assump_3048
                                case intro assump_3070 assump_3071 =>
                                  apply Or.inl
                                  intro assump_3076
                                  apply And.intro
                                  cases assump_3076
                                  case intro assump_3077 assump_3078 =>
                                    apply False.elim assump_3077
                                  cases assump_3076
                                  case intro assump_3081 assump_3082 =>
                                    apply False.elim assump_3081
                          case inr assump_3042 =>
                            cases assump_3038
                            case intro assump_3089 assump_3090 =>
                              cases assump_3089
                              case inl assump_3091 =>
                                cases assump_3090
                                case intro assump_3095 assump_3096 =>
                                  apply Or.inl
                                  intro assump_3101
                                  apply And.intro
                                  cases assump_3101
                                  case intro assump_3102 assump_3103 =>
                                    apply False.elim assump_3102
                                  cases assump_3101
                                  case intro assump_3106 assump_3107 =>
                                    apply False.elim assump_3106
                              case inr assump_3092 =>
                                cases assump_3090
                                case intro assump_3112 assump_3113 =>
                                  apply Or.inl
                                  intro assump_3118
                                  apply And.intro
                                  cases assump_3118
                                  case intro assump_3119 assump_3120 =>
                                    apply False.elim assump_3119
                                  cases assump_3118
                                  case intro assump_3123 assump_3124 =>
                                    apply False.elim assump_3123
                    case inr assump_3034 =>
                      cases assump_2346
                      case intro assump_3129 assump_3130 =>
                        cases assump_3129
                        case intro assump_3131 assump_3132 =>
                          cases assump_3131
                          case inl assump_3133 =>
                            cases assump_3130
                            case intro assump_3139 assump_3140 =>
                              cases assump_3139
                              case inl assump_3141 =>
                                cases assump_3140
                                case intro assump_3145 assump_3146 =>
                                  apply Or.inl
                                  intro assump_3151
                                  apply And.intro
                                  cases assump_3151
                                  case intro assump_3152 assump_3153 =>
                                    apply False.elim assump_3152
                                  cases assump_3151
                                  case intro assump_3156 assump_3157 =>
                                    apply False.elim assump_3156
                              case inr assump_3142 =>
                                cases assump_3140
                                case intro assump_3162 assump_3163 =>
                                  apply Or.inl
                                  intro assump_3168
                                  apply And.intro
                                  cases assump_3168
                                  case intro assump_3169 assump_3170 =>
                                    apply False.elim assump_3169
                                  cases assump_3168
                                  case intro assump_3173 assump_3174 =>
                                    apply False.elim assump_3173
                          case inr assump_3134 =>
                            cases assump_3130
                            case intro assump_3181 assump_3182 =>
                              cases assump_3181
                              case inl assump_3183 =>
                                cases assump_3182
                                case intro assump_3187 assump_3188 =>
                                  apply Or.inl
                                  intro assump_3193
                                  apply And.intro
                                  cases assump_3193
                                  case intro assump_3194 assump_3195 =>
                                    apply False.elim assump_3194
                                  cases assump_3193
                                  case intro assump_3198 assump_3199 =>
                                    apply False.elim assump_3198
                              case inr assump_3184 =>
                                cases assump_3182
                                case intro assump_3204 assump_3205 =>
                                  apply Or.inl
                                  intro assump_3210
                                  apply And.intro
                                  cases assump_3210
                                  case intro assump_3211 assump_3212 =>
                                    apply False.elim assump_3211
                                  cases assump_3210
                                  case intro assump_3215 assump_3216 =>
                                    apply False.elim assump_3215
                case inr assump_2932 =>
                  cases assump_2348
                  case inl assump_3221 =>
                    cases assump_3221
                    case intro assump_3223 assump_3224 =>
                      cases assump_2346
                      case intro assump_3229 assump_3230 =>
                        cases assump_3229
                        case intro assump_3231 assump_3232 =>
                          cases assump_3231
                          case inl assump_3233 =>
                            cases assump_3230
                            case intro assump_3239 assump_3240 =>
                              cases assump_3239
                              case inl assump_3241 =>
                                cases assump_3240
                                case intro assump_3245 assump_3246 =>
                                  apply Or.inl
                                  intro assump_3251
                                  apply And.intro
                                  cases assump_3251
                                  case intro assump_3252 assump_3253 =>
                                    apply False.elim assump_3252
                                  cases assump_3251
                                  case intro assump_3256 assump_3257 =>
                                    apply False.elim assump_3256
                              case inr assump_3242 =>
                                cases assump_3240
                                case intro assump_3262 assump_3263 =>
                                  apply Or.inl
                                  intro assump_3268
                                  apply And.intro
                                  cases assump_3268
                                  case intro assump_3269 assump_3270 =>
                                    apply False.elim assump_3269
                                  cases assump_3268
                                  case intro assump_3273 assump_3274 =>
                                    apply False.elim assump_3273
                          case inr assump_3234 =>
                            cases assump_3230
                            case intro assump_3281 assump_3282 =>
                              cases assump_3281
                              case inl assump_3283 =>
                                cases assump_3282
                                case intro assump_3287 assump_3288 =>
                                  apply Or.inl
                                  intro assump_3293
                                  apply And.intro
                                  cases assump_3293
                                  case intro assump_3294 assump_3295 =>
                                    apply False.elim assump_3294
                                  cases assump_3293
                                  case intro assump_3298 assump_3299 =>
                                    apply False.elim assump_3298
                              case inr assump_3284 =>
                                cases assump_3282
                                case intro assump_3304 assump_3305 =>
                                  apply Or.inl
                                  intro assump_3310
                                  apply And.intro
                                  cases assump_3310
                                  case intro assump_3311 assump_3312 =>
                                    apply False.elim assump_3311
                                  cases assump_3310
                                  case intro assump_3315 assump_3316 =>
                                    apply False.elim assump_3315
                  case inr assump_3222 =>
                    cases assump_3222
                    case inl assump_3319 =>
                      cases assump_2346
                      case intro assump_3323 assump_3324 =>
                        cases assump_3323
                        case intro assump_3325 assump_3326 =>
                          cases assump_3325
                          case inl assump_3327 =>
                            cases assump_3324
                            case intro assump_3333 assump_3334 =>
                              cases assump_3333
                              case inl assump_3335 =>
                                cases assump_3334
                                case intro assump_3339 assump_3340 =>
                                  apply Or.inl
                                  intro assump_3345
                                  apply And.intro
                                  cases assump_3345
                                  case intro assump_3346 assump_3347 =>
                                    apply False.elim assump_3346
                                  cases assump_3345
                                  case intro assump_3350 assump_3351 =>
                                    apply False.elim assump_3350
                              case inr assump_3336 =>
                                cases assump_3334
                                case intro assump_3356 assump_3357 =>
                                  apply Or.inl
                                  intro assump_3362
                                  apply And.intro
                                  cases assump_3362
                                  case intro assump_3363 assump_3364 =>
                                    apply False.elim assump_3363
                                  cases assump_3362
                                  case intro assump_3367 assump_3368 =>
                                    apply False.elim assump_3367
                          case inr assump_3328 =>
                            cases assump_3324
                            case intro assump_3375 assump_3376 =>
                              cases assump_3375
                              case inl assump_3377 =>
                                cases assump_3376
                                case intro assump_3381 assump_3382 =>
                                  apply Or.inl
                                  intro assump_3387
                                  apply And.intro
                                  cases assump_3387
                                  case intro assump_3388 assump_3389 =>
                                    apply False.elim assump_3388
                                  cases assump_3387
                                  case intro assump_3392 assump_3393 =>
                                    apply False.elim assump_3392
                              case inr assump_3378 =>
                                cases assump_3376
                                case intro assump_3398 assump_3399 =>
                                  apply Or.inl
                                  intro assump_3404
                                  apply And.intro
                                  cases assump_3404
                                  case intro assump_3405 assump_3406 =>
                                    apply False.elim assump_3405
                                  cases assump_3404
                                  case intro assump_3409 assump_3410 =>
                                    apply False.elim assump_3409
                    case inr assump_3320 =>
                      cases assump_2346
                      case intro assump_3415 assump_3416 =>
                        cases assump_3415
                        case intro assump_3417 assump_3418 =>
                          cases assump_3417
                          case inl assump_3419 =>
                            cases assump_3416
                            case intro assump_3425 assump_3426 =>
                              cases assump_3425
                              case inl assump_3427 =>
                                cases assump_3426
                                case intro assump_3431 assump_3432 =>
                                  apply Or.inl
                                  intro assump_3437
                                  apply And.intro
                                  cases assump_3437
                                  case intro assump_3438 assump_3439 =>
                                    apply False.elim assump_3438
                                  cases assump_3437
                                  case intro assump_3442 assump_3443 =>
                                    apply False.elim assump_3442
                              case inr assump_3428 =>
                                cases assump_3426
                                case intro assump_3448 assump_3449 =>
                                  apply Or.inl
                                  intro assump_3454
                                  apply And.intro
                                  cases assump_3454
                                  case intro assump_3455 assump_3456 =>
                                    apply False.elim assump_3455
                                  cases assump_3454
                                  case intro assump_3459 assump_3460 =>
                                    apply False.elim assump_3459
                          case inr assump_3420 =>
                            cases assump_3416
                            case intro assump_3467 assump_3468 =>
                              cases assump_3467
                              case inl assump_3469 =>
                                cases assump_3468
                                case intro assump_3473 assump_3474 =>
                                  apply Or.inl
                                  intro assump_3479
                                  apply And.intro
                                  cases assump_3479
                                  case intro assump_3480 assump_3481 =>
                                    apply False.elim assump_3480
                                  cases assump_3479
                                  case intro assump_3484 assump_3485 =>
                                    apply False.elim assump_3484
                              case inr assump_3470 =>
                                cases assump_3468
                                case intro assump_3490 assump_3491 =>
                                  apply Or.inl
                                  intro assump_3496
                                  apply And.intro
                                  cases assump_3496
                                  case intro assump_3497 assump_3498 =>
                                    apply False.elim assump_3497
                                  cases assump_3496
                                  case intro assump_3501 assump_3502 =>
                                    apply False.elim assump_3501


variable (p7 p2 p5 p0 p4 p1 p6 p3 : Prop)
theorem file39_187719 : (((((True → False) ∧ (p7 ∨ False)) ∨ ((p2 ∨ p2) ∧ (False ∨ p7))) → (((p5 ∨ p2) → (p2 → p2)) ∨ ((True ∨ p1) ∨ (False ∨ p2)))) ∨ ((((p6 ∨ p1) → (p3 ∨ True)) ∨ ((p5 → p7) → (p4 ∨ p2))) ∨ (((p3 ∧ p6) ∧ (p5 → p0)) → ((p0 → p5) ∨ (p5 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        cases assump_12
        case inl assump_16 =>
          exact assump_13
        case inr assump_17 =>
          exact assump_17
      case inr assump_9 =>
        apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case intro assump_24 assump_25 =>
      cases assump_24
      case inl assump_26 =>
        cases assump_25
        case inl assump_30 =>
          apply False.elim assump_30
        case inr assump_31 =>
          apply Or.inl
          intro assump_36
          intro assump_37
          cases assump_36
          case inl assump_40 =>
            exact assump_37
          case inr assump_41 =>
            exact assump_41
      case inr assump_27 =>
        cases assump_25
        case inl assump_48 =>
          apply False.elim assump_48
        case inr assump_49 =>
          apply Or.inl
          intro assump_54
          intro assump_55
          cases assump_54
          case inl assump_58 =>
            exact assump_55
          case inr assump_59 =>
            exact assump_59


variable (p5 p6 p4 p3 p2 p7 : Prop)
theorem file39_189309 : (((((p7 ∨ p7) → False) → False) ∨ (((p4 → p3) → (p4 → p2)) → False)) → ((((p3 ∧ p2) ∧ (p5 ∨ False)) ∨ ((False → False) ∨ (p3 → False))) ∨ (((p6 → False) → False) → ((p3 ∧ p7) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p6 p0 p2 p3 p7 p4 p5 : Prop)
theorem file39_189847 : ((((((p6 ∧ p0) ∧ (p4 → False)) → ((p0 ∨ p4) → False)) → False) ∧ ((((False ∨ p3) ∨ (p4 ∧ p5)) → ((p2 ∨ p7) ∨ (True ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((False ∨ p3) ∨ (p4 ∧ p5)) → ((p2 ∨ p7) ∨ (True ∨ p2))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply Or.inr
          apply Or.inl
          apply True.intro
      case inr assump_11 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply Or.inr
          apply Or.inl
          apply True.intro
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8


variable (p0 p7 p6 p4 p2 p1 p3 : Prop)
theorem file39_190710 : ((((((p6 → False) ∨ (True ∨ p7)) → False) ∧ (((p3 → True) ∨ (p2 ∧ p1)) ∧ ((False → False) → (p0 → p4)))) ∧ ((((p4 → False) → False) ∧ ((p3 → p3) → (p4 → False))) ∨ (((p7 ∧ p1) → False) ∧ ((False ∧ p1) ∧ (p6 ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_102 : (p4 → False) := by
                intro assump_30
                have assump_103 : (p3 → p3) := by
                  intro assump_35
                  exact assump_35
                let assump_34 := assump_19 assump_103
                have assump_104 : p4 := by
                  exact assump_30
                let assump_38 := assump_34 assump_104
                apply False.elim assump_38
              let assump_29 := assump_18 assump_102
              apply False.elim assump_29
          case inr assump_17 =>
            cases assump_17
            case intro assump_45 assump_46 =>
              cases assump_46
              case intro assump_49 assump_50 =>
                cases assump_49
                case intro assump_51 assump_52 =>
                  apply False.elim assump_51
        case inr assump_11 =>
          cases assump_11
          case intro assump_55 assump_56 =>
            cases assump_3
            case inl assump_63 =>
              cases assump_63
              case intro assump_65 assump_66 =>
                have assump_105 : (p4 → False) := by
                  intro assump_77
                  have assump_106 : (p3 → p3) := by
                    intro assump_82
                    exact assump_82
                  let assump_81 := assump_66 assump_106
                  have assump_107 : p4 := by
                    exact assump_77
                  let assump_85 := assump_81 assump_107
                  apply False.elim assump_85
                let assump_76 := assump_65 assump_105
                apply False.elim assump_76
            case inr assump_64 =>
              cases assump_64
              case intro assump_92 assump_93 =>
                cases assump_93
                case intro assump_96 assump_97 =>
                  cases assump_96
                  case intro assump_98 assump_99 =>
                    apply False.elim assump_98


variable (p4 p0 p7 p5 p3 p6 : Prop)
theorem file39_193313 : (((((p5 → False) → False) → ((p5 ∨ p6) ∧ (p3 ∨ p7))) → False) → ((((p3 → p7) → (True → p0)) ∨ ((p7 → False) → False)) → (((False → False) → (True ∨ p3)) ∨ ((p5 ∨ True) ∧ (p5 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    apply Or.inl
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    intro assump_16
    apply Or.inl
    apply True.intro


variable (p3 p4 p5 p1 p6 p2 : Prop)
theorem file39_193809 : ((((((True → False) → (p5 ∨ p4)) → ((p2 → False) → (True ∨ p3))) ∨ (((p6 → p1) → False) ∨ ((p1 → p5) → (False ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((True → False) → (p5 ∨ p4)) → ((p2 → False) → (True ∨ p3))) ∨ (((p6 → p1) → False) ∨ ((p1 → p5) → (False ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p0 p7 p1 p2 p3 p6 p4 : Prop)
theorem file39_194335 : (((((p3 ∧ p6) ∧ (p5 → True)) ∧ ((p1 → False) ∨ (p0 ∧ p5))) ∨ (((p0 ∧ p4) ∧ (p0 → False)) → ((p5 → False) ∨ (p5 → p6)))) ∨ ((((True → False) ∧ (p1 → False)) ∨ ((p0 ∧ False) → (False → p7))) ∨ (((p2 → p0) ∨ (p7 → p1)) → False))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      have assump_20 : p0 := by
        exact assump_4
      let assump_16 := assump_3 assump_20
      apply False.elim assump_16


variable (p0 p6 p3 p5 p4 p2 p7 : Prop)
theorem file39_194955 : ((((((p4 ∧ p7) → False) ∨ ((p0 → False) → (True → False))) ∧ (((False → p4) ∨ (p5 ∧ p0)) → False)) ∨ ((((p3 ∧ False) ∧ (p0 ∨ True)) ∧ ((p3 → False) → False)) ∧ (((False ∨ p7) ∨ (p7 → p2)) ∧ ((p7 ∧ p7) ∧ (p6 → False))))) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        have assump_46 : ((False → p4) ∨ (p5 ∧ p0)) := by
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_9 assump_46
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_47 : ((False → p4) ∨ (p5 ∧ p0)) := by
          apply Or.inl
          intro assump_28
          apply False.elim assump_28
        let assump_27 := assump_9 assump_47
        apply False.elim assump_27
  case inr assump_7 =>
    cases assump_7
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_41


variable (p1 p4 p0 p3 p2 : Prop)
theorem file39_196199 : ((((((True → False) → (p0 → p2)) → ((p3 → True) → (False → p1))) ∨ (((p0 ∨ p1) → False) ∨ ((p3 → p4) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((True → False) → (p0 → p2)) → ((p3 → True) → (False → p1))) ∨ (((p0 ∨ p1) → False) ∨ ((p3 → p4) ∨ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p6 p1 p3 p7 p0 p2 : Prop)
theorem file39_196733 : (((((p0 ∨ p2) ∨ (False ∨ p7)) ∨ ((p2 → False) → (p0 ∧ False))) ∧ (((p3 ∧ p2) → (p3 ∨ p3)) → False)) → ((((p5 ∨ p7) ∨ (p3 → p3)) → ((p2 → p3) ∧ (p3 ∨ p2))) → (((p6 ∨ p6) → False) ∧ ((p1 ∨ p3) ∧ (p0 → p2))))) := by
  intro assump_69
  intro assump_70
  apply And.intro
  intro assump_71
  cases assump_71
  case inl assump_72 =>
    cases assump_69
    case intro assump_78 assump_79 =>
      cases assump_78
      case inl assump_80 =>
        cases assump_80
        case inl assump_82 =>
          cases assump_82
          case inl assump_84 =>
            have assump_366 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_91
              cases assump_91
              case intro assump_92 assump_93 =>
                apply Or.inl
                exact assump_92
            let assump_90 := assump_79 assump_366
            apply False.elim assump_90
          case inr assump_85 =>
            have assump_367 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_106
              cases assump_106
              case intro assump_107 assump_108 =>
                apply Or.inl
                exact assump_107
            let assump_105 := assump_79 assump_367
            apply False.elim assump_105
        case inr assump_83 =>
          cases assump_83
          case inl assump_116 =>
            apply False.elim assump_116
          case inr assump_117 =>
            have assump_368 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_125
              cases assump_125
              case intro assump_126 assump_127 =>
                apply Or.inl
                exact assump_126
            let assump_124 := assump_79 assump_368
            apply False.elim assump_124
      case inr assump_81 =>
        have assump_369 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
          intro assump_140
          cases assump_140
          case intro assump_141 assump_142 =>
            apply Or.inl
            exact assump_141
        let assump_139 := assump_79 assump_369
        apply False.elim assump_139
  case inr assump_73 =>
    cases assump_69
    case intro assump_154 assump_155 =>
      cases assump_154
      case inl assump_156 =>
        cases assump_156
        case inl assump_158 =>
          cases assump_158
          case inl assump_160 =>
            have assump_370 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_167
              cases assump_167
              case intro assump_168 assump_169 =>
                apply Or.inl
                exact assump_168
            let assump_166 := assump_155 assump_370
            apply False.elim assump_166
          case inr assump_161 =>
            have assump_371 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_182
              cases assump_182
              case intro assump_183 assump_184 =>
                apply Or.inl
                exact assump_183
            let assump_181 := assump_155 assump_371
            apply False.elim assump_181
        case inr assump_159 =>
          cases assump_159
          case inl assump_192 =>
            apply False.elim assump_192
          case inr assump_193 =>
            have assump_372 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
              intro assump_201
              cases assump_201
              case intro assump_202 assump_203 =>
                apply Or.inl
                exact assump_202
            let assump_200 := assump_155 assump_372
            apply False.elim assump_200
      case inr assump_157 =>
        have assump_373 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
          intro assump_216
          cases assump_216
          case intro assump_217 assump_218 =>
            apply Or.inl
            exact assump_217
        let assump_215 := assump_155 assump_373
        apply False.elim assump_215
  apply And.intro
  cases assump_69
  case intro assump_228 assump_229 =>
    cases assump_228
    case inl assump_230 =>
      cases assump_230
      case inl assump_232 =>
        cases assump_232
        case inl assump_234 =>
          have assump_374 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
            intro assump_241
            cases assump_241
            case intro assump_242 assump_243 =>
              apply Or.inl
              exact assump_242
          let assump_240 := assump_229 assump_374
          apply False.elim assump_240
        case inr assump_235 =>
          have assump_375 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
            intro assump_256
            cases assump_256
            case intro assump_257 assump_258 =>
              apply Or.inl
              exact assump_257
          let assump_255 := assump_229 assump_375
          apply False.elim assump_255
      case inr assump_233 =>
        cases assump_233
        case inl assump_266 =>
          apply False.elim assump_266
        case inr assump_267 =>
          have assump_376 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
            intro assump_275
            cases assump_275
            case intro assump_276 assump_277 =>
              apply Or.inl
              exact assump_276
          let assump_274 := assump_229 assump_376
          apply False.elim assump_274
    case inr assump_231 =>
      have assump_377 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
        intro assump_290
        cases assump_290
        case intro assump_291 assump_292 =>
          apply Or.inl
          exact assump_291
      let assump_289 := assump_229 assump_377
      apply False.elim assump_289
  intro assump_300
  cases assump_69
  case intro assump_305 assump_306 =>
    cases assump_305
    case inl assump_307 =>
      cases assump_307
      case inl assump_309 =>
        cases assump_309
        case inl assump_311 =>
          have assump_378 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
            intro assump_318
            cases assump_318
            case intro assump_319 assump_320 =>
              apply Or.inl
              exact assump_319
          let assump_317 := assump_306 assump_378
          apply False.elim assump_317
        case inr assump_312 =>
          exact assump_312
      case inr assump_310 =>
        cases assump_310
        case inl assump_332 =>
          apply False.elim assump_332
        case inr assump_333 =>
          have assump_379 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
            intro assump_341
            cases assump_341
            case intro assump_342 assump_343 =>
              apply Or.inl
              exact assump_342
          let assump_340 := assump_306 assump_379
          apply False.elim assump_340
    case inr assump_308 =>
      have assump_380 : ((p3 ∧ p2) → (p3 ∨ p3)) := by
        intro assump_356
        cases assump_356
        case intro assump_357 assump_358 =>
          apply Or.inl
          exact assump_357
      let assump_355 := assump_306 assump_380
      apply False.elim assump_355


variable (p3 p6 p2 p0 p4 p5 p1 p7 : Prop)
theorem file39_203597 : ((((((p6 ∧ p3) → False) ∧ ((p0 → p4) ∨ (False ∨ p6))) → (((p5 ∧ p1) → False) ∨ ((p6 ∧ p2) ∨ (p7 → False)))) ∧ ((((p3 → True) → False) → ((p1 → False) ∨ (False ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p3 → True) → False) → ((p1 → False) ∨ (False ∨ p4))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      have assump_25 : (p3 → True) := by
        intro assump_17
        apply True.intro
      let assump_16 := assump_9 assump_25
      apply False.elim assump_16
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p7 p5 p1 p3 : Prop)
theorem file39_204290 : (((((p1 ∨ True) → False) ∧ ((p5 → False) ∧ (p5 ∨ True))) → False) ∨ ((((p3 ∧ True) → (p3 → False)) ∨ ((False → False) ∨ (p5 ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_26 : p5 := by
          exact assump_10
        let assump_15 := assump_6 assump_26
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_27 : (p1 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_2 assump_27
        apply False.elim assump_22


variable (p4 p7 p6 p5 p2 p0 p3 : Prop)
theorem file39_205027 : (((((False → p3) → (p0 → p7)) → ((p6 ∧ p5) → (p4 ∨ p5))) ∨ (((p7 ∧ p6) → False) ∧ ((p4 ∨ p7) ∨ (p6 → False)))) ∨ ((((p0 ∧ p5) → False) → False) ∨ (((p3 ∨ p3) → False) ∧ ((False ∨ p5) → (p2 → p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    exact assump_4


variable (p0 p4 p7 p6 p2 p5 p1 : Prop)
theorem file39_205446 : (((((p6 ∧ p1) → (p1 ∧ p4)) → ((True → p0) → (p6 ∧ False))) ∧ (((p7 → False) ∨ (p7 ∧ p0)) ∧ ((p6 → p4) ∨ (False → False)))) → ((((p1 ∨ p2) → (False → True)) ∨ ((p6 → False) → (p5 ∧ p1))) ∨ (((p0 → p6) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          intro assump_16
          intro assump_17
          apply True.intro
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_20
          intro assump_21
          apply True.intro
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          cases assump_7
          case inl assump_28 =>
            apply Or.inl
            apply Or.inl
            intro assump_32
            intro assump_33
            apply True.intro
          case inr assump_29 =>
            apply Or.inl
            apply Or.inl
            intro assump_36
            intro assump_37
            apply True.intro


variable (p4 p3 p0 p5 p6 p1 p2 : Prop)
theorem file39_206690 : (((((False ∧ p6) → False) ∨ ((p1 ∧ p0) ∨ (p6 → False))) → False) → ((((p3 ∨ p1) ∨ (True ∧ p6)) → False) ∨ (((p2 → False) → (p5 ∧ p4)) → ((False ∧ p2) ∧ (p4 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_49 : (((False ∧ p6) → False) ∨ ((p1 ∧ p0) ∨ (p6 → False))) := by
        apply Or.inl
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      let assump_12 := assump_1 assump_49
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_50 : (((False ∧ p6) → False) ∨ ((p1 ∧ p0) ∨ (p6 → False))) := by
        apply Or.inl
        intro assump_25
        cases assump_25
        case intro assump_26 assump_27 =>
          apply False.elim assump_26
      let assump_24 := assump_1 assump_50
      apply False.elim assump_24
  case inr assump_6 =>
    cases assump_6
    case intro assump_33 assump_34 =>
      have assump_51 : (((False ∧ p6) → False) ∨ ((p1 ∧ p0) ∨ (p6 → False))) := by
        apply Or.inl
        intro assump_41
        cases assump_41
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      let assump_40 := assump_1 assump_51
      apply False.elim assump_40


variable (p7 p3 p2 p1 p0 p5 p4 : Prop)
theorem file39_208084 : ((((((p1 → False) ∨ (False → False)) ∧ ((False → False) ∧ (False ∧ p3))) ∧ (((p7 ∧ p2) → False) ∧ ((p7 ∨ True) ∨ (p2 → p5)))) ∧ ((((p5 ∧ False) ∨ (p4 ∧ p2)) → ((p3 → p0) ∨ (p7 ∧ p3))) → False)) → False) := by
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
            cases assump_13
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
        case inr assump_9 =>
          cases assump_7
          case intro assump_22 assump_23 =>
            cases assump_23
            case intro assump_26 assump_27 =>
              apply False.elim assump_26


variable (p5 p3 p7 p0 p2 p4 : Prop)
theorem file39_208984 : (((((p5 ∧ False) → (False ∨ p3)) ∨ ((p0 → False) → (p3 → False))) → (((True ∧ p5) ∧ (True → p3)) ∧ ((p0 ∨ True) → False))) → ((((p0 → False) → (p5 ∧ True)) ∧ ((False ∨ True) → False)) → (((p2 ∧ p0) → False) → ((p7 ∨ p0) ∨ (p4 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_33 : (((p5 ∧ False) → (False ∨ p3)) ∨ ((p0 → False) → (p3 → False))) := by
      apply Or.inl
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    let assump_14 := assump_1 assump_33
    let assump_22 := And.right assump_14
    have assump_34 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_29 := assump_22 assump_34
    apply False.elim assump_29


variable (p2 p6 p1 p0 p5 : Prop)
theorem file39_209848 : (((((False → p0) ∨ (p1 → False)) ∧ ((p2 ∧ True) → (True ∧ True))) ∨ (((p5 → False) ∨ (False → p6)) ∧ ((p0 → False) ∨ (p6 → False)))) ∧ ((((p0 ∧ False) → False) → False) → False)) := by
  apply And.intro
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_5
  have assump_19 : ((p0 ∧ False) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p0 p2 p6 p3 p1 p5 p7 : Prop)
theorem file39_210519 : (((((p3 → False) → False) ∧ ((p2 ∨ p5) ∨ (False → p6))) → (((False ∧ p2) → False) ∨ ((False ∧ p2) → False))) ∧ ((((p3 ∨ True) → False) → ((False ∨ p7) → (p0 ∨ p1))) ∨ (((True ∧ p2) → False) → ((p0 ∧ p2) → (True → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_9 =>
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
    case inr assump_7 =>
      apply Or.inl
      intro assump_26
      cases assump_26
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
  apply Or.inl
  intro assump_31
  intro assump_32
  cases assump_32
  case inl assump_33 =>
    apply False.elim assump_33
  case inr assump_34 =>
    have assump_45 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_41 := assump_31 assump_45
    apply False.elim assump_41


variable (p6 p7 p1 p3 : Prop)
theorem file39_211768 : (((((p1 ∨ p6) → (p7 → p7)) ∨ ((False → p3) ∨ (p6 → True))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p1 ∨ p6) → (p7 → p7)) ∨ ((False → p3) ∨ (p6 → True))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      exact assump_6
    case inr assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p3 p4 p5 p7 p0 : Prop)
theorem file39_212242 : ((((((p1 ∨ p3) ∧ (True ∧ p4)) ∨ ((False ∨ False) ∨ (False → False))) ∨ (((p4 ∧ p1) → (p0 ∨ p7)) → ((False → p7) ∧ (p5 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 ∨ p3) ∧ (True ∧ p4)) ∨ ((False ∨ False) ∨ (False → False))) ∨ (((p4 ∧ p1) → (p0 ∨ p7)) → ((False → p7) ∧ (p5 ∧ p0)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p4 p1 p2 p7 p5 : Prop)
theorem file39_212785 : ((((((p0 → False) ∧ (True ∨ p5)) → ((True → False) → False)) ∨ (((True ∨ False) ∧ (p1 → False)) ∧ ((p0 ∧ False) → False))) ∧ ((((p2 ∨ p2) ∧ (p7 ∨ p5)) ∧ ((p5 ∨ p4) → (p0 → False))) ∧ (((True ∧ False) → False) → False))) → False) := by
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
            case inl assump_14 =>
              cases assump_13
              case inl assump_18 =>
                have assump_190 : ((True ∧ False) → False) := by
                  intro assump_27
                  cases assump_27
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_29
                let assump_26 := assump_9 assump_190
                apply False.elim assump_26
              case inr assump_19 =>
                have assump_191 : ((True ∧ False) → False) := by
                  intro assump_44
                  cases assump_44
                  case intro assump_45 assump_46 =>
                    apply False.elim assump_46
                let assump_43 := assump_9 assump_191
                apply False.elim assump_43
            case inr assump_15 =>
              cases assump_13
              case inl assump_56 =>
                have assump_192 : ((True ∧ False) → False) := by
                  intro assump_65
                  cases assump_65
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_67
                let assump_64 := assump_9 assump_192
                apply False.elim assump_64
              case inr assump_57 =>
                have assump_193 : ((True ∧ False) → False) := by
                  intro assump_82
                  cases assump_82
                  case intro assump_83 assump_84 =>
                    apply False.elim assump_84
                let assump_81 := assump_9 assump_193
                apply False.elim assump_81
    case inr assump_5 =>
      cases assump_5
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_94
          case inl assump_96 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_104
              case intro assump_106 assump_107 =>
                cases assump_106
                case intro assump_108 assump_109 =>
                  cases assump_108
                  case inl assump_110 =>
                    cases assump_109
                    case inl assump_114 =>
                      have assump_194 : ((True ∧ False) → False) := by
                        intro assump_123
                        cases assump_123
                        case intro assump_124 assump_125 =>
                          apply False.elim assump_125
                      let assump_122 := assump_105 assump_194
                      apply False.elim assump_122
                    case inr assump_115 =>
                      have assump_195 : ((True ∧ False) → False) := by
                        intro assump_140
                        cases assump_140
                        case intro assump_141 assump_142 =>
                          apply False.elim assump_142
                      let assump_139 := assump_105 assump_195
                      apply False.elim assump_139
                  case inr assump_111 =>
                    cases assump_109
                    case inl assump_152 =>
                      have assump_196 : ((True ∧ False) → False) := by
                        intro assump_161
                        cases assump_161
                        case intro assump_162 assump_163 =>
                          apply False.elim assump_163
                      let assump_160 := assump_105 assump_196
                      apply False.elim assump_160
                    case inr assump_153 =>
                      have assump_197 : ((True ∧ False) → False) := by
                        intro assump_178
                        cases assump_178
                        case intro assump_179 assump_180 =>
                          apply False.elim assump_180
                      let assump_177 := assump_105 assump_197
                      apply False.elim assump_177
          case inr assump_97 =>
            apply False.elim assump_97


variable (p3 p2 : Prop)
theorem file39_217387 : ((((((p3 ∨ p3) → (p2 → False)) ∧ ((False → p2) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 ∨ p3) → (p2 → False)) ∧ ((False → p2) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_23 : (False → p2) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p6 p0 p5 p1 p2 : Prop)
theorem file39_217958 : (((((p1 ∧ p0) ∧ (p5 ∧ p5)) → ((p5 ∨ True) ∨ (False ∧ p7))) → False) → ((((p2 ∨ p5) → False) → ((p6 → p0) → False)) ∧ (((p6 ∧ p7) ∨ (p2 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_86 : (((p1 ∧ p0) ∧ (p5 ∧ p5)) → ((p5 ∨ True) ∨ (False ∧ p7))) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inl
          exact assump_21
  let assump_10 := assump_1 assump_86
  apply False.elim assump_10
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      have assump_87 : (((p1 ∧ p0) ∧ (p5 ∧ p5)) → ((p5 ∨ True) ∨ (False ∧ p7))) := by
        intro assump_41
        cases assump_41
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_43
            case intro assump_50 assump_51 =>
              apply Or.inl
              apply Or.inl
              exact assump_51
      let assump_40 := assump_1 assump_87
      apply False.elim assump_40
  case inr assump_31 =>
    cases assump_31
    case intro assump_59 assump_60 =>
      have assump_88 : (((p1 ∧ p0) ∧ (p5 ∧ p5)) → ((p5 ∨ True) ∨ (False ∧ p7))) := by
        intro assump_68
        cases assump_68
        case intro assump_69 assump_70 =>
          cases assump_69
          case intro assump_71 assump_72 =>
            cases assump_70
            case intro assump_77 assump_78 =>
              apply Or.inl
              apply Or.inl
              exact assump_78
      let assump_67 := assump_1 assump_88
      apply False.elim assump_67


variable (p4 p1 p7 p5 p0 p2 p6 p3 : Prop)
theorem file39_219837 : (((((p4 ∧ p6) → False) ∧ ((p4 ∧ False) → False)) ∨ (((p7 → False) → (True → False)) ∧ ((p2 → p0) ∧ (False → p5)))) → ((((p0 ∧ p1) → (p1 → False)) → ((False → False) ∨ (False ∧ p0))) → (((False → p0) ∨ (True ∨ p5)) ∧ ((p3 ∧ p5) → (p6 → p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
  case inr assump_6 =>
    cases assump_6
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        apply Or.inl
        intro assump_26
        apply False.elim assump_26
  intro assump_29
  intro assump_30
  cases assump_29
  case intro assump_33 assump_34 =>
    cases assump_1
    case inl assump_41 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        exact assump_33
    case inr assump_42 =>
      cases assump_42
      case intro assump_49 assump_50 =>
        cases assump_50
        case intro assump_53 assump_54 =>
          exact assump_33


variable (p2 p4 p7 p6 p5 p3 p0 p1 : Prop)
theorem file39_220996 : (((((p7 ∨ p6) ∨ (True → p0)) ∨ ((p0 ∨ p5) → False)) ∨ (((p6 ∧ False) → False) ∧ ((p6 → p3) ∧ (p2 → False)))) → ((((False ∧ p4) ∧ (p5 ∨ p1)) ∧ ((p3 → False) ∨ (p3 → True))) → (((True → False) → False) ∨ ((p3 → True) ∧ (p7 → p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p5 p2 p0 p4 p7 : Prop)
theorem file39_221523 : ((((((p5 → False) ∧ (p0 ∧ p0)) ∧ ((p5 ∧ p4) ∨ (p2 ∨ p4))) → (((p7 ∧ False) ∧ (p7 ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 → False) ∧ (p0 ∧ p0)) ∧ ((p5 ∧ p4) ∨ (p2 ∨ p4))) → (((p7 ∧ False) ∧ (p7 ∧ True)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p2 p0 p3 p5 p7 : Prop)
theorem file39_222100 : ((((((p7 ∧ p2) ∧ (p0 → True)) ∨ ((p3 ∧ p2) ∧ (p6 ∧ False))) → (((p7 → False) → (p2 → False)) ∨ ((False → p0) ∧ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_45 : ((((p7 ∧ p2) ∧ (p0 → True)) ∨ ((p3 ∧ p2) ∧ (p6 ∧ False))) → (((p7 → False) → (p2 → False)) ∨ ((False → p0) ∧ (p5 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_18
          intro assump_19
          have assump_46 : p7 := by
            exact assump_10
          let assump_24 := assump_18 assump_46
          apply False.elim assump_24
    case inr assump_7 =>
      cases assump_7
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_29
          case intro assump_36 assump_37 =>
            apply False.elim assump_37
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p4 p1 p0 p2 p7 p6 p5 : Prop)
theorem file39_223217 : (((((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) → False) → ((((p2 ∨ p1) ∨ (p7 → False)) ∧ ((False ∧ p7) ∧ (p1 ∨ p0))) ∧ (((True → p4) ∨ (p6 → p5)) ∧ ((p2 → False) ∨ (p5 ∨ p1))))) := by
  intro assump_12
  apply And.intro
  apply And.intro
  apply Or.inr
  intro assump_15
  have assump_90 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      apply False.elim assump_21
  let assump_19 := assump_12 assump_90
  apply False.elim assump_19
  apply And.intro
  apply And.intro
  have assump_91 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply False.elim assump_32
  let assump_30 := assump_12 assump_91
  apply False.elim assump_30
  have assump_92 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_42
    cases assump_42
    case intro assump_43 assump_44 =>
      apply False.elim assump_43
  let assump_41 := assump_12 assump_92
  apply False.elim assump_41
  have assump_93 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_53
    cases assump_53
    case intro assump_54 assump_55 =>
      apply False.elim assump_54
  let assump_52 := assump_12 assump_93
  apply False.elim assump_52
  apply And.intro
  apply Or.inl
  intro assump_63
  have assump_94 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_67
    cases assump_67
    case intro assump_68 assump_69 =>
      apply False.elim assump_68
  let assump_66 := assump_12 assump_94
  apply False.elim assump_66
  apply Or.inl
  intro assump_77
  have assump_95 : (((p4 ∧ p1) ∧ (p2 → False)) ∨ ((False ∧ True) → False)) := by
    apply Or.inr
    intro assump_82
    cases assump_82
    case intro assump_83 assump_84 =>
      apply False.elim assump_83
  let assump_81 := assump_12 assump_95
  apply False.elim assump_81


variable (p5 p7 p2 p3 p1 p4 : Prop)
theorem file39_225341 : ((((((p5 → p5) → False) → ((p3 → False) ∨ (p4 → p1))) ∨ (((p2 → p2) → False) ∨ ((p7 → p5) ∧ (p3 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 → p5) → False) → ((p3 → False) ∨ (p4 → p1))) ∨ (((p2 → p2) → False) ∨ ((p7 → p5) ∧ (p3 ∨ True)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (p5 → p5) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p6 : Prop)
theorem file39_225956 : (((((False → p6) ∧ (False → False)) ∨ ((False ∨ False) ∧ (False → p1))) → False) → False) := by
  intro assump_1
  have assump_14 : (((False → p6) ∧ (False → False)) ∨ ((False ∨ False) ∧ (False → p1))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p5 p6 p4 p2 p7 p3 : Prop)
theorem file39_226427 : (((((p3 ∧ p2) ∧ (p2 ∧ True)) ∧ ((p3 ∧ p6) → (p3 ∨ p7))) ∧ (((p7 → False) → False) ∧ ((p3 → False) → False))) ∨ ((((p1 → p4) ∧ (True → p5)) ∧ ((False ∧ p7) ∧ (True ∨ p3))) → False)) := by
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p7 p6 p0 p5 p1 p4 : Prop)
theorem file39_226976 : ((((((p5 → p1) → (p5 → False)) ∧ ((p1 ∧ p1) ∧ (p6 → False))) → (((p5 ∧ p7) ∧ (p4 → p7)) → ((p4 ∧ p6) ∧ (p0 → True)))) ∧ ((((p6 → p4) → False) → ((False → False) ∨ (False → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p6 → p4) → False) → ((False → False) ∨ (False → True))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p7 p5 p4 p1 : Prop)
theorem file39_227553 : ((((((p1 ∨ p7) → (True ∧ p5)) → ((False → p4) → False)) → (((p5 ∨ p4) ∧ (p5 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p1 ∨ p7) → (True ∧ p5)) → ((False → p4) → False)) → (((p5 ∨ p4) ∧ (p5 ∨ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          have assump_65 : ((p1 ∨ p7) → (True ∧ p5)) := by
            intro assump_20
            apply And.intro
            apply True.intro
            cases assump_20
            case inl assump_21 =>
              exact assump_13
            case inr assump_22 =>
              exact assump_13
          let assump_19 := assump_5 assump_65
          have assump_66 : (False → p4) := by
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_19 assump_66
          apply False.elim assump_27
        case inr assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case inl assump_38 =>
          have assump_67 : ((p1 ∨ p7) → (True ∧ p5)) := by
            intro assump_45
            apply And.intro
            apply True.intro
            cases assump_45
            case inl assump_46 =>
              exact assump_38
            case inr assump_47 =>
              exact assump_38
          let assump_44 := assump_5 assump_67
          have assump_68 : (False → p4) := by
            intro assump_53
            apply False.elim assump_53
          let assump_52 := assump_44 assump_68
          apply False.elim assump_52
        case inr assump_39 =>
          apply False.elim assump_39
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p3 p2 p0 p7 p1 p6 : Prop)
theorem file39_229429 : ((((((False ∨ p3) ∨ (p6 → False)) → ((p0 ∧ p1) → (p3 ∨ p1))) → (((False ∧ p6) ∧ (p2 → False)) → False)) ∧ ((((p6 → False) → False) → False) ∧ (((p0 ∧ p7) → (p3 ∨ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((p0 ∧ p7) → (p3 ∨ p7)) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply Or.inr
          exact assump_15
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p2 p4 p6 p7 p3 : Prop)
theorem file39_230069 : (((((p7 ∧ p3) ∧ (True → p6)) → False) → (((True → p2) → (False → p6)) → ((p4 ∨ p7) ∨ (True ∧ True)))) ∨ ((((p4 ∧ True) → False) → False) → False)) := by
  apply Or.inl
  intro assump_17
  intro assump_18
  apply Or.inr
  apply And.intro
  apply True.intro
  apply True.intro


variable (p7 p5 p4 p6 p3 p2 p1 : Prop)
theorem file39_230407 : (((((p7 → False) ∧ (False ∧ p7)) → False) ∨ (((p2 ∧ True) → (p1 ∧ False)) ∧ ((p5 → False) → (p4 → False)))) ∨ ((((False → False) ∨ (p5 → False)) → ((p6 → False) → False)) ∨ (((p3 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p2 p0 p1 p7 p3 p4 : Prop)
theorem file39_230866 : (((((True ∨ True) → (p1 → False)) → False) ∧ (((False → False) ∧ (p1 ∨ False)) ∧ ((False ∧ p4) ∧ (True → False)))) → ((((p7 → p2) ∨ (p4 ∧ p0)) → False) ∧ (((p1 ∧ True) ∧ (p1 ∨ p3)) ∧ ((p4 → p0) ∧ (p1 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            cases assump_12
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                apply False.elim assump_23
          case inr assump_18 =>
            apply False.elim assump_18
  case inr assump_4 =>
    cases assump_4
    case intro assump_29 assump_30 =>
      cases assump_1
      case intro assump_35 assump_36 =>
        cases assump_36
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            cases assump_42
            case inl assump_45 =>
              cases assump_40
              case intro assump_49 assump_50 =>
                cases assump_49
                case intro assump_51 assump_52 =>
                  apply False.elim assump_51
            case inr assump_46 =>
              apply False.elim assump_46
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_57 assump_58 =>
    cases assump_58
    case intro assump_61 assump_62 =>
      cases assump_61
      case intro assump_63 assump_64 =>
        cases assump_64
        case inl assump_67 =>
          cases assump_62
          case intro assump_71 assump_72 =>
            cases assump_71
            case intro assump_73 assump_74 =>
              apply False.elim assump_73
        case inr assump_68 =>
          apply False.elim assump_68
  apply True.intro
  cases assump_1
  case intro assump_79 assump_80 =>
    cases assump_80
    case intro assump_83 assump_84 =>
      cases assump_83
      case intro assump_85 assump_86 =>
        cases assump_86
        case inl assump_89 =>
          cases assump_84
          case intro assump_93 assump_94 =>
            cases assump_93
            case intro assump_95 assump_96 =>
              apply False.elim assump_95
        case inr assump_90 =>
          apply False.elim assump_90
  apply And.intro
  intro assump_101
  cases assump_1
  case intro assump_104 assump_105 =>
    cases assump_105
    case intro assump_108 assump_109 =>
      cases assump_108
      case intro assump_110 assump_111 =>
        cases assump_111
        case inl assump_114 =>
          cases assump_109
          case intro assump_118 assump_119 =>
            cases assump_118
            case intro assump_120 assump_121 =>
              apply False.elim assump_120
        case inr assump_115 =>
          apply False.elim assump_115
  intro assump_126
  cases assump_1
  case intro assump_129 assump_130 =>
    cases assump_130
    case intro assump_133 assump_134 =>
      cases assump_133
      case intro assump_135 assump_136 =>
        cases assump_136
        case inl assump_139 =>
          cases assump_134
          case intro assump_143 assump_144 =>
            cases assump_143
            case intro assump_145 assump_146 =>
              apply False.elim assump_145
        case inr assump_140 =>
          apply False.elim assump_140


variable (p2 p1 p5 p6 p4 p3 p0 : Prop)
theorem file39_234448 : (((((True → p3) ∧ (p2 ∧ p1)) ∧ ((p5 → p3) → (p4 → False))) → (((p2 ∧ p2) ∧ (True ∨ False)) ∨ ((p0 ∨ p5) ∨ (p4 ∨ p2)))) ∨ ((((False → False) ∧ (p6 ∧ False)) ∨ ((p5 → p3) ∨ (p2 ∨ p6))) → (((p4 → p4) ∨ (p3 ∨ p0)) → ((p6 → p1) ∧ (p6 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply And.intro
        apply And.intro
        exact assump_8
        exact assump_8
        apply Or.inl
        apply True.intro


variable (p2 p1 p6 p3 p5 p4 p0 : Prop)
theorem file39_235114 : (((((p1 ∨ p2) ∨ (True ∧ True)) → ((p5 ∧ p2) ∧ (p4 ∧ p6))) ∧ (((p0 → False) ∨ (p1 → False)) → ((False → False) ∧ (p0 → False)))) → ((((False → False) → False) → ((p2 → p3) ∨ (True → False))) ∨ (((True ∨ p4) ∧ (p3 → p4)) ∧ ((False → p1) ∨ (p1 → True))))) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply Or.inl
    intro assump_17
    apply Or.inl
    intro assump_20
    have assump_31 : (False → False) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_17 assump_31
    apply False.elim assump_24


variable (p6 p3 p0 p5 p1 p7 : Prop)
theorem file39_235749 : (((((p7 ∧ p5) ∧ (p1 ∧ p0)) ∨ ((False → False) ∧ (p3 → False))) → (((p3 → False) ∧ (p3 → False)) ∧ ((p3 → p5) ∧ (False ∨ p0)))) → ((((p0 ∨ p6) → False) → ((p6 → False) → False)) → (((False → p1) → False) → ((p3 ∧ p1) → (p0 ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    apply True.intro


variable (p2 p6 p0 p7 p1 : Prop)
theorem file39_236203 : ((((((p6 ∧ p6) → (True ∨ p7)) ∨ ((p6 ∨ p2) → False)) ∨ (((p7 → p0) → False) → ((p1 ∨ True) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∧ p6) → (True ∨ p7)) ∨ ((p6 ∨ p2) → False)) ∨ (((p7 → p0) → False) → ((p1 ∨ True) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p4 p3 p0 p2 p7 p1 : Prop)
theorem file39_236749 : (((((p7 ∧ p5) ∧ (p1 → False)) → False) → (((p3 ∨ True) → False) → ((False → False) ∨ (p5 → p1)))) ∨ ((((p0 → p7) → False) → ((p0 ∨ p4) ∨ (True → p3))) → (((p2 → False) ∧ (True → p3)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p0 p5 p6 p1 p7 p3 : Prop)
theorem file39_237118 : ((((((p0 ∧ p5) ∨ (p1 ∨ p5)) → ((p1 ∨ p5) ∧ (p3 ∨ True))) ∧ (((p7 ∧ p6) ∧ (p0 → False)) ∨ ((False ∨ p1) → False))) ∧ ((((False ∧ True) → False) ∧ ((p6 ∨ True) ∨ (p7 ∧ p7))) → False)) → False) := by
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
          case intro assump_12 assump_13 =>
            have assump_44 : (((False ∧ True) → False) ∧ ((p6 ∨ True) ∨ (p7 ∧ p7))) := by
              apply And.intro
              intro assump_23
              cases assump_23
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
              apply Or.inl
              apply Or.inl
              exact assump_13
            let assump_22 := assump_3 assump_44
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_45 : (((False ∧ True) → False) ∧ ((p6 ∨ True) ∨ (p7 ∧ p7))) := by
          apply And.intro
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_35 := assump_3 assump_45
        apply False.elim assump_35


variable (p2 p4 p3 p0 p5 : Prop)
theorem file39_238546 : ((((((p3 ∨ p4) ∧ (p3 → p0)) ∨ ((False ∨ p5) → (p3 → p5))) ∨ (((False ∨ p2) ∧ (p4 ∧ p0)) ∨ ((True → False) → (p5 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∨ p4) ∧ (p3 → p0)) ∨ ((False ∨ p5) → (p3 → p5))) ∨ (((False ∨ p2) ∧ (p4 ∧ p0)) ∨ ((True → False) → (p5 ∨ p0)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      exact assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p2 p1 p7 p3 p6 p4 : Prop)
theorem file39_239176 : (((((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) → False) → ((((p7 ∨ p2) ∨ (p4 ∧ p2)) → ((p3 ∨ p4) → (p6 ∨ False))) ∨ (((p5 ∧ p3) ∧ (p3 → p4)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        have assump_148 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_19
          intro assump_20
          intro assump_21
          exact assump_12
        let assump_18 := assump_1 assump_148
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_149 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_36
          intro assump_37
          intro assump_38
          have assump_150 : (p2 ∨ p1) := by
            apply Or.inl
            exact assump_13
          let assump_45 := assump_36 assump_150
          apply False.elim assump_45
        let assump_35 := assump_1 assump_149
        apply False.elim assump_35
    case inr assump_11 =>
      cases assump_11
      case intro assump_52 assump_53 =>
        have assump_151 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_62
          intro assump_63
          intro assump_64
          have assump_152 : (p2 ∨ p1) := by
            apply Or.inl
            exact assump_53
          let assump_71 := assump_62 assump_152
          apply False.elim assump_71
        let assump_61 := assump_1 assump_151
        apply False.elim assump_61
  case inr assump_7 =>
    cases assump_4
    case inl assump_80 =>
      cases assump_80
      case inl assump_82 =>
        have assump_153 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_89
          intro assump_90
          intro assump_91
          exact assump_82
        let assump_88 := assump_1 assump_153
        apply False.elim assump_88
      case inr assump_83 =>
        have assump_154 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_106
          intro assump_107
          intro assump_108
          have assump_155 : (p2 ∨ p1) := by
            apply Or.inl
            exact assump_83
          let assump_115 := assump_106 assump_155
          apply False.elim assump_115
        let assump_105 := assump_1 assump_154
        apply False.elim assump_105
    case inr assump_81 =>
      cases assump_81
      case intro assump_122 assump_123 =>
        have assump_156 : (((p2 ∨ p1) → False) → ((p3 → False) → (p6 → p7))) := by
          intro assump_132
          intro assump_133
          intro assump_134
          have assump_157 : (p2 ∨ p1) := by
            apply Or.inl
            exact assump_123
          let assump_141 := assump_132 assump_157
          apply False.elim assump_141
        let assump_131 := assump_1 assump_156
        apply False.elim assump_131


variable (p4 p7 p3 p5 p1 : Prop)
theorem file39_242193 : (((((p3 → p1) → False) ∧ ((False → False) → False)) ∧ (((p7 ∨ p4) → (False → p1)) ∨ ((True ∧ p3) ∧ (p1 → False)))) → ((((p3 → False) ∧ (p5 → p1)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        have assump_44 : (False → False) := by
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_8 assump_44
        apply False.elim assump_18
      case inr assump_14 =>
        cases assump_14
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            have assump_45 : (False → False) := by
              intro assump_38
              apply False.elim assump_38
            let assump_37 := assump_8 assump_45
            apply False.elim assump_37


variable (p1 p4 p7 p2 p6 p3 p0 : Prop)
theorem file39_243178 : (((((False → False) ∨ (p1 ∧ p3)) ∨ ((p7 → p1) ∧ (p4 ∨ p6))) → (((p7 → False) → (p6 ∨ p2)) → ((p6 ∨ True) ∨ (False → p2)))) ∧ ((((p3 ∧ p1) → False) ∧ ((p1 ∧ p1) ∧ (p2 ∧ p3))) → (((p3 ∨ p1) → (False → True)) ∧ ((p0 ∧ False) ∨ (p4 ∧ p4))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_22 =>
        apply Or.inl
        apply Or.inl
        exact assump_22
  intro assump_27
  apply And.intro
  intro assump_28
  intro assump_29
  apply True.intro
  cases assump_27
  case intro assump_30 assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        cases assump_35
        case intro assump_42 assump_43 =>
          have assump_56 : (p3 ∧ p1) := by
            apply And.intro
            exact assump_43
            exact assump_37
          let assump_52 := assump_30 assump_56
          apply False.elim assump_52


variable (p3 p2 p6 p7 p0 p4 : Prop)
theorem file39_244665 : (((((p3 ∨ p2) ∨ (p6 ∧ False)) → False) ∧ (((False → p0) ∨ (p3 → False)) ∧ ((p2 → False) ∨ (p0 → False)))) → ((((p2 → p0) ∧ (True → False)) → ((True → p0) ∨ (p7 → False))) ∧ (((p4 ∨ p0) → False) → ((True ∨ p7) ∧ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case inl assump_19 =>
            apply Or.inl
            intro assump_23
            have assump_149 : True := by
              apply True.intro
            let assump_29 := assump_4 assump_149
            apply False.elim assump_29
          case inr assump_20 =>
            apply Or.inl
            intro assump_35
            have assump_150 : True := by
              apply True.intro
            let assump_41 := assump_4 assump_150
            apply False.elim assump_41
        case inr assump_16 =>
          cases assump_14
          case inl assump_47 =>
            apply Or.inl
            intro assump_51
            have assump_151 : True := by
              apply True.intro
            let assump_57 := assump_4 assump_151
            apply False.elim assump_57
          case inr assump_48 =>
            apply Or.inl
            intro assump_63
            have assump_152 : True := by
              apply True.intro
            let assump_69 := assump_4 assump_152
            apply False.elim assump_69
  intro assump_73
  apply And.intro
  cases assump_1
  case intro assump_76 assump_77 =>
    cases assump_77
    case intro assump_80 assump_81 =>
      cases assump_80
      case inl assump_82 =>
        cases assump_81
        case inl assump_86 =>
          apply Or.inl
          apply True.intro
        case inr assump_87 =>
          apply Or.inl
          apply True.intro
      case inr assump_83 =>
        cases assump_81
        case inl assump_94 =>
          apply Or.inl
          apply True.intro
        case inr assump_95 =>
          apply Or.inl
          apply True.intro
  intro assump_100
  cases assump_1
  case intro assump_105 assump_106 =>
    cases assump_106
    case intro assump_109 assump_110 =>
      cases assump_109
      case inl assump_111 =>
        cases assump_110
        case inl assump_115 =>
          have assump_153 : p2 := by
            exact assump_100
          let assump_119 := assump_115 assump_153
          apply False.elim assump_119
        case inr assump_116 =>
          have assump_154 : ((p3 ∨ p2) ∨ (p6 ∧ False)) := by
            apply Or.inl
            apply Or.inr
            exact assump_100
          let assump_127 := assump_105 assump_154
          apply False.elim assump_127
      case inr assump_112 =>
        cases assump_110
        case inl assump_133 =>
          have assump_155 : p2 := by
            exact assump_100
          let assump_137 := assump_133 assump_155
          apply False.elim assump_137
        case inr assump_134 =>
          have assump_156 : ((p3 ∨ p2) ∨ (p6 ∧ False)) := by
            apply Or.inl
            apply Or.inr
            exact assump_100
          let assump_145 := assump_105 assump_156
          apply False.elim assump_145


variable (p6 p3 p0 p4 p5 : Prop)
theorem file39_248040 : ((((((p0 ∨ p6) → False) ∨ ((p3 → False) → (p6 ∨ p4))) → (((p4 ∧ p3) → False) → ((p4 ∨ p5) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 ∨ p6) → False) ∨ ((p3 → False) → (p6 ∨ p4))) → (((p4 ∧ p3) → False) → ((p4 ∨ p5) → (False → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p5 p3 p4 p2 p7 p1 p0 : Prop)
theorem file39_248563 : (((((p0 ∧ p2) ∧ (p0 ∨ True)) → False) ∨ (((p5 → False) ∨ (p7 → p7)) → ((True ∨ p7) → (p2 → p2)))) → ((((p6 ∨ p6) ∧ (p7 ∨ p4)) ∧ ((p3 ∧ p1) → (p7 ∨ False))) → (((p5 → False) → (False → p4)) ∧ ((p3 ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p7 p5 p2 p1 : Prop)
theorem file39_249052 : ((((((p2 → p2) → False) ∧ ((p5 ∧ p1) → (p7 ∨ p1))) → False) → False) → False) := by
  intro assump_16
  have assump_38 : ((((p2 → p2) → False) ∧ ((p5 ∧ p1) → (p7 ∨ p1))) → False) := by
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      have assump_39 : (p2 → p2) := by
        intro assump_29
        exact assump_29
      let assump_28 := assump_21 assump_39
      apply False.elim assump_28
  let assump_19 := assump_16 assump_38
  apply False.elim assump_19


variable (p0 p4 p6 p3 p1 p2 p5 : Prop)
theorem file39_249609 : ((((((p4 ∧ p0) → (p4 → p5)) → ((p5 → p0) → (p4 ∧ p1))) ∨ (((True ∨ p0) → (p1 ∧ p2)) → False)) ∧ ((((p2 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p3 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_22 : (((p2 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p3 ∨ p6))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_10 := assump_3 assump_22
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_23 : (((p2 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p3 ∨ p6))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_18 := assump_3 assump_23
      apply False.elim assump_18


variable (p1 p2 p5 p7 p4 p6 : Prop)
theorem file39_250483 : (((((p1 ∨ p1) ∧ (p2 → False)) → ((False ∧ p7) → False)) ∧ (((p4 ∧ False) → False) → False)) → ((((p5 ∨ p1) ∧ (p6 ∧ p5)) → ((p5 ∧ p4) → False)) ∧ (((True ∧ p5) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          cases assump_1
          case intro assump_22 assump_23 =>
            have assump_84 : ((p4 ∧ False) → False) := by
              intro assump_29
              cases assump_29
              case intro assump_30 assump_31 =>
                apply False.elim assump_31
            let assump_28 := assump_23 assump_84
            apply False.elim assump_28
      case inr assump_13 =>
        cases assump_11
        case intro assump_41 assump_42 =>
          cases assump_1
          case intro assump_47 assump_48 =>
            have assump_85 : ((p4 ∧ False) → False) := by
              intro assump_54
              cases assump_54
              case intro assump_55 assump_56 =>
                apply False.elim assump_56
            let assump_53 := assump_48 assump_85
            apply False.elim assump_53
  intro assump_64
  cases assump_1
  case intro assump_67 assump_68 =>
    have assump_86 : ((p4 ∧ False) → False) := by
      intro assump_74
      cases assump_74
      case intro assump_75 assump_76 =>
        apply False.elim assump_76
    let assump_73 := assump_68 assump_86
    apply False.elim assump_73


variable (p2 p6 p3 p5 p1 p7 p0 p4 : Prop)
theorem file39_252165 : (((((p5 ∧ p0) ∧ (p0 → p3)) ∨ ((p4 ∧ p1) ∧ (False → False))) ∨ (((p0 ∧ p7) ∧ (p3 ∨ p2)) ∨ ((False ∧ p6) → False))) ∨ ((((p2 ∧ p6) ∨ (p3 → p5)) ∨ ((p0 ∧ p7) ∧ (p0 ∧ p2))) ∨ (((p7 → False) → (p0 → p6)) → ((p0 ∧ p0) → False)))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


