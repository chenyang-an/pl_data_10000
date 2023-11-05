variable (p7 p3 p5 : Prop)
theorem file23_35 : ((((((p3 ∧ p5) ∨ (p7 ∧ p5)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p3 ∧ p5) ∨ (p7 ∧ p5)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_44 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_7 assump_44
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_25 assump_26 =>
          have assump_45 : (False → False) := by
            intro assump_34
            apply False.elim assump_34
          let assump_33 := assump_7 assump_45
          apply False.elim assump_33
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p1 p0 p6 p3 p7 p4 : Prop)
theorem file23_1033 : ((((((p0 → p6) ∨ (p0 → False)) → ((True ∧ p6) → (p6 ∨ p7))) ∨ (((p4 → False) ∧ (p3 ∨ p1)) → ((p0 ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 → p6) ∨ (p0 → False)) → ((True ∧ p6) → (p6 ∨ p7))) ∨ (((p4 → False) ∧ (p3 ∨ p1)) → ((p0 ∨ p7) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        apply Or.inl
        exact assump_8
      case inr assump_14 =>
        apply Or.inl
        exact assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p3 p2 p7 p0 p4 : Prop)
theorem file23_1725 : ((((((p7 ∨ False) → (p6 → False)) → ((False → p7) ∧ (p2 ∨ p2))) → (((p3 ∧ p3) ∨ (False → False)) ∨ ((p0 ∨ p4) → (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p7 ∨ False) → (p6 → False)) → ((False → p7) ∧ (p2 ∨ p2))) → (((p3 ∧ p3) ∨ (False → False)) ∨ ((p0 ∨ p4) → (p7 ∧ False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p4 p0 p3 p2 p7 p5 : Prop)
theorem file23_2275 : (((((p5 ∧ p5) ∧ (p7 ∧ p2)) → ((p4 → False) → (p2 → False))) → (((p4 → p3) ∧ (False → False)) → ((p5 ∧ p5) ∨ (False → p2)))) ∨ ((((False → False) ∧ (p0 ∧ p0)) → ((False ∨ p7) ∨ (False ∧ p0))) ∧ (((False → False) ∨ (p7 → False)) ∨ ((p6 → False) ∨ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    intro assump_11
    apply False.elim assump_11


variable (p4 p5 p7 p3 p1 p0 p6 : Prop)
theorem file23_2774 : (((((False ∧ True) → (True ∧ True)) → ((p4 ∧ p1) ∨ (p1 → False))) → (((False ∨ p6) ∧ (p7 ∧ p1)) → ((p0 → True) ∧ (p1 → p7)))) ∨ ((((p4 ∧ p0) → (p0 → False)) ∧ ((p5 → p7) ∧ (p6 ∧ p3))) → False)) := by
  apply Or.inl
  intro assump_20
  intro assump_21
  apply And.intro
  intro assump_22
  apply True.intro
  intro assump_23
  cases assump_21
  case intro assump_26 assump_27 =>
    cases assump_26
    case inl assump_28 =>
      apply False.elim assump_28
    case inr assump_29 =>
      cases assump_27
      case intro assump_34 assump_35 =>
        exact assump_34


variable (p6 p5 p7 p3 p4 p0 p2 : Prop)
theorem file23_3406 : (((((p0 → False) ∨ (p6 ∨ p3)) → ((p0 → p3) → False)) ∧ (((p6 ∧ p6) → False) ∧ ((p4 → False) ∧ (p0 → False)))) → ((((p3 → p7) → False) ∨ ((p0 ∨ p6) → (p2 ∨ p4))) ∨ (((p5 ∧ p2) → (False ∧ p7)) → ((True → p5) ∨ (p0 → p5))))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply Or.inl
        apply Or.inl
        intro assump_24
        have assump_54 : ((p0 → False) ∨ (p6 ∨ p3)) := by
          apply Or.inl
          intro assump_32
          have assump_55 : p0 := by
            exact assump_32
          let assump_37 := assump_19 assump_55
          apply False.elim assump_37
        let assump_31 := assump_10 assump_54
        have assump_56 : (p0 → p3) := by
          intro assump_42
          have assump_57 : p0 := by
            exact assump_42
          let assump_47 := assump_19 assump_57
          apply False.elim assump_47
        let assump_41 := assump_31 assump_56
        apply False.elim assump_41


variable (p4 p6 p5 p7 p0 p3 p2 : Prop)
theorem file23_4548 : (((((p7 → False) → False) ∧ ((p6 → p3) → False)) ∧ (((p3 ∨ True) → False) ∧ ((False → False) → (p2 → False)))) → ((((p3 ∧ p2) ∧ (p4 ∧ p4)) ∨ ((p7 ∧ p2) → False)) ∨ (((p5 → p4) ∨ (p5 ∧ p0)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inr
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          have assump_33 : (False → False) := by
            intro assump_26
            apply False.elim assump_26
          let assump_25 := assump_11 assump_33
          have assump_34 : p2 := by
            exact assump_18
          let assump_29 := assump_25 assump_34
          apply False.elim assump_29


variable (p7 p6 p2 p5 p3 p0 p1 p4 : Prop)
theorem file23_5447 : (((((p3 ∧ p5) → (p7 → False)) ∧ ((p5 ∨ p1) → False)) → (((p2 → False) ∧ (False ∨ p2)) → False)) ∨ ((((True → False) ∧ (p2 ∧ p5)) ∧ ((p6 ∧ p2) → (p4 ∧ False))) ∨ (((p4 → p6) → (p2 → p0)) → ((p3 ∧ p1) ∨ (p7 → p5))))) := by
  apply Or.inl
  intro assump_9
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case inl assump_15 =>
      apply False.elim assump_15
    case inr assump_16 =>
      cases assump_9
      case intro assump_21 assump_22 =>
        have assump_34 : p2 := by
          exact assump_16
        let assump_30 := assump_11 assump_34
        apply False.elim assump_30


variable (p3 p6 p2 p4 p1 p5 p0 : Prop)
theorem file23_6141 : (((((True ∧ True) → (p4 → True)) ∨ ((p1 ∧ True) → (p6 ∨ p2))) ∨ (((p0 → False) ∨ (True ∨ p5)) → ((p4 ∧ p1) ∨ (p5 → True)))) ∨ ((((p6 ∧ True) → (p6 ∨ p0)) ∨ ((p0 → p3) ∨ (p3 ∨ p0))) → (((True ∨ True) ∧ (p5 ∨ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p1 p7 p3 p4 p0 p2 : Prop)
theorem file23_6528 : ((((((p4 → False) → (p4 ∧ p2)) → False) → (((True → p2) → False) ∨ ((p0 ∨ True) → False))) ∧ ((((False ∨ True) → (p7 → False)) ∧ ((p1 → p3) → False)) ∧ (((False → False) → False) ∧ ((False ∧ p3) ∨ (p0 → p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_15
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_20
          case inr assump_19 =>
            have assump_34 : (False → False) := by
              intro assump_28
              apply False.elim assump_28
            let assump_27 := assump_14 assump_34
            apply False.elim assump_27


variable (p4 p5 p7 p6 p1 p3 p0 p2 : Prop)
theorem file23_7482 : (((((False ∨ False) → (p6 → False)) → False) ∧ (((p3 → False) ∧ (p3 ∨ p5)) ∧ ((p0 ∨ p7) ∧ (p0 → p4)))) → ((((p0 ∧ p4) ∧ (p4 ∨ p6)) → ((p5 ∧ p5) → False)) ∨ (((p4 ∧ p2) → False) ∨ ((p1 → p4) → False)))) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_32
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        cases assump_38
        case inl assump_41 =>
          cases assump_36
          case intro assump_45 assump_46 =>
            cases assump_45
            case inl assump_47 =>
              apply Or.inl
              intro assump_53
              intro assump_54
              cases assump_54
              case intro assump_55 assump_56 =>
                cases assump_53
                case intro assump_61 assump_62 =>
                  cases assump_61
                  case intro assump_63 assump_64 =>
                    cases assump_62
                    case inl assump_69 =>
                      have assump_307 : p3 := by
                        exact assump_41
                      let assump_82 := assump_37 assump_307
                      apply False.elim assump_82
                    case inr assump_70 =>
                      have assump_308 : p3 := by
                        exact assump_41
                      let assump_97 := assump_37 assump_308
                      apply False.elim assump_97
            case inr assump_48 =>
              apply Or.inl
              intro assump_105
              intro assump_106
              cases assump_106
              case intro assump_107 assump_108 =>
                cases assump_105
                case intro assump_113 assump_114 =>
                  cases assump_113
                  case intro assump_115 assump_116 =>
                    cases assump_114
                    case inl assump_121 =>
                      have assump_309 : p3 := by
                        exact assump_41
                      let assump_134 := assump_37 assump_309
                      apply False.elim assump_134
                    case inr assump_122 =>
                      have assump_310 : p3 := by
                        exact assump_41
                      let assump_149 := assump_37 assump_310
                      apply False.elim assump_149
        case inr assump_42 =>
          cases assump_36
          case intro assump_155 assump_156 =>
            cases assump_155
            case inl assump_157 =>
              apply Or.inl
              intro assump_163
              intro assump_164
              cases assump_164
              case intro assump_165 assump_166 =>
                cases assump_163
                case intro assump_171 assump_172 =>
                  cases assump_171
                  case intro assump_173 assump_174 =>
                    cases assump_172
                    case inl assump_179 =>
                      have assump_311 : ((False ∨ False) → (p6 → False)) := by
                        intro assump_194
                        intro assump_195
                        cases assump_194
                        case inl assump_198 =>
                          apply False.elim assump_198
                        case inr assump_199 =>
                          apply False.elim assump_199
                      let assump_193 := assump_31 assump_311
                      apply False.elim assump_193
                    case inr assump_180 =>
                      have assump_312 : ((False ∨ False) → (p6 → False)) := by
                        intro assump_220
                        intro assump_221
                        cases assump_220
                        case inl assump_224 =>
                          apply False.elim assump_224
                        case inr assump_225 =>
                          apply False.elim assump_225
                      let assump_219 := assump_31 assump_312
                      apply False.elim assump_219
            case inr assump_158 =>
              apply Or.inl
              intro assump_237
              intro assump_238
              cases assump_238
              case intro assump_239 assump_240 =>
                cases assump_237
                case intro assump_245 assump_246 =>
                  cases assump_245
                  case intro assump_247 assump_248 =>
                    cases assump_246
                    case inl assump_253 =>
                      have assump_313 : ((False ∨ False) → (p6 → False)) := by
                        intro assump_268
                        intro assump_269
                        cases assump_268
                        case inl assump_272 =>
                          apply False.elim assump_272
                        case inr assump_273 =>
                          apply False.elim assump_273
                      let assump_267 := assump_31 assump_313
                      apply False.elim assump_267
                    case inr assump_254 =>
                      have assump_314 : ((False ∨ False) → (p6 → False)) := by
                        intro assump_294
                        intro assump_295
                        cases assump_294
                        case inl assump_298 =>
                          apply False.elim assump_298
                        case inr assump_299 =>
                          apply False.elim assump_299
                      let assump_293 := assump_31 assump_314
                      apply False.elim assump_293


variable (p2 p1 : Prop)
theorem file23_13061 : ((((((p2 → p2) ∨ (p1 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → p2) ∨ (p1 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p2 → p2) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p0 p7 p6 p3 p4 p5 p1 : Prop)
theorem file23_13557 : (((((False → True) → False) ∧ ((p7 ∨ p6) ∧ (p1 → p5))) → (((p3 ∨ p2) ∧ (p2 ∨ False)) ∧ ((p3 → p3) ∧ (False → False)))) ∨ ((((p4 ∨ p5) → False) ∨ ((p2 ∨ p0) ∧ (p3 → False))) ∨ (((p7 ∧ p0) ∧ (p6 → False)) ∧ ((p6 ∨ p3) ∧ (p5 ∨ p5))))) := by
  apply Or.inl
  intro assump_9
  apply And.intro
  apply And.intro
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        have assump_92 : (False → True) := by
          intro assump_25
          apply True.intro
        let assump_24 := assump_10 assump_92
        apply False.elim assump_24
      case inr assump_17 =>
        have assump_93 : (False → True) := by
          intro assump_36
          apply True.intro
        let assump_35 := assump_10 assump_93
        apply False.elim assump_35
  cases assump_9
  case intro assump_40 assump_41 =>
    cases assump_41
    case intro assump_44 assump_45 =>
      cases assump_44
      case inl assump_46 =>
        have assump_94 : (False → True) := by
          intro assump_55
          apply True.intro
        let assump_54 := assump_40 assump_94
        apply False.elim assump_54
      case inr assump_47 =>
        have assump_95 : (False → True) := by
          intro assump_66
          apply True.intro
        let assump_65 := assump_40 assump_95
        apply False.elim assump_65
  apply And.intro
  intro assump_70
  cases assump_9
  case intro assump_73 assump_74 =>
    cases assump_74
    case intro assump_77 assump_78 =>
      cases assump_77
      case inl assump_79 =>
        exact assump_70
      case inr assump_80 =>
        exact assump_70
  intro assump_89
  apply False.elim assump_89


variable (p1 p6 p0 p3 p2 : Prop)
theorem file23_15334 : ((((((p3 ∨ True) ∨ (p1 → False)) → False) → (((False ∧ False) ∧ (False ∧ p6)) → False)) → ((((p0 → p0) ∨ (p2 → True)) → ((p2 → p2) ∨ (p1 → False))) → False)) → False) := by
  intro assump_1
  have assump_30 : ((((p3 ∨ True) ∨ (p1 → False)) → False) → (((False ∧ False) ∧ (False ∧ p6)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_30
  have assump_31 : (((p0 → p0) ∨ (p2 → True)) → ((p2 → p2) ∨ (p1 → False))) := by
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      apply Or.inl
      intro assump_19
      exact assump_19
    case inr assump_16 =>
      apply Or.inl
      intro assump_24
      exact assump_24
  let assump_13 := assump_4 assump_31
  apply False.elim assump_13


variable (p4 p7 p2 p6 p3 p1 : Prop)
theorem file23_16286 : ((((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_182 : ((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        intro assump_13
        cases assump_12
        case intro assump_16 assump_17 =>
          have assump_183 : ((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) := by
            intro assump_26
            cases assump_26
            case inl assump_27 =>
              cases assump_27
              case inl assump_29 =>
                apply Or.inl
                apply And.intro
                apply Or.inl
                apply True.intro
                apply Or.inl
                exact assump_16
              case inr assump_30 =>
                apply Or.inl
                apply And.intro
                apply Or.inl
                apply True.intro
                apply Or.inl
                exact assump_16
            case inr assump_28 =>
              cases assump_28
              case intro assump_35 assump_36 =>
                cases assump_35
                case inl assump_37 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_16
                case inr assump_38 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_16
          let assump_25 := assump_1 assump_183
          apply False.elim assump_25
      case inr assump_9 =>
        apply Or.inr
        intro assump_52
        intro assump_53
        cases assump_52
        case intro assump_56 assump_57 =>
          have assump_184 : ((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) := by
            intro assump_66
            cases assump_66
            case inl assump_67 =>
              cases assump_67
              case inl assump_69 =>
                apply Or.inl
                apply And.intro
                apply Or.inl
                apply True.intro
                apply Or.inl
                exact assump_56
              case inr assump_70 =>
                apply Or.inl
                apply And.intro
                apply Or.inl
                apply True.intro
                apply Or.inl
                exact assump_56
            case inr assump_68 =>
              cases assump_68
              case intro assump_75 assump_76 =>
                cases assump_75
                case inl assump_77 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_56
                case inr assump_78 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_56
          let assump_65 := assump_1 assump_184
          apply False.elim assump_65
    case inr assump_7 =>
      cases assump_7
      case intro assump_90 assump_91 =>
        cases assump_90
        case inl assump_92 =>
          apply Or.inr
          intro assump_98
          intro assump_99
          cases assump_98
          case intro assump_102 assump_103 =>
            have assump_185 : ((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) := by
              intro assump_112
              cases assump_112
              case inl assump_113 =>
                cases assump_113
                case inl assump_115 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_102
                case inr assump_116 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_102
              case inr assump_114 =>
                cases assump_114
                case intro assump_121 assump_122 =>
                  cases assump_121
                  case inl assump_123 =>
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    exact assump_102
                  case inr assump_124 =>
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    exact assump_102
            let assump_111 := assump_1 assump_185
            apply False.elim assump_111
        case inr assump_93 =>
          apply Or.inr
          intro assump_140
          intro assump_141
          cases assump_140
          case intro assump_144 assump_145 =>
            have assump_186 : ((((p4 → p3) ∨ (p4 → p4)) ∨ ((True ∨ p1) ∧ (p6 → False))) → (((True ∨ p7) ∧ (p7 ∨ p6)) ∨ ((p7 ∧ p2) → (True → False)))) := by
              intro assump_155
              cases assump_155
              case inl assump_156 =>
                cases assump_156
                case inl assump_158 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_144
                case inr assump_159 =>
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  apply True.intro
                  apply Or.inl
                  exact assump_144
              case inr assump_157 =>
                cases assump_157
                case intro assump_164 assump_165 =>
                  cases assump_164
                  case inl assump_166 =>
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    exact assump_144
                  case inr assump_167 =>
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    apply Or.inl
                    exact assump_144
            let assump_154 := assump_1 assump_186
            apply False.elim assump_154
  let assump_4 := assump_1 assump_182
  apply False.elim assump_4


variable (p2 p3 p1 p0 p5 : Prop)
theorem file23_23427 : (((((p3 ∧ False) → (p5 ∨ p1)) ∨ ((p0 ∨ p2) → False)) → False) → ((((p3 ∧ False) ∨ (p1 → p0)) ∧ ((p5 ∨ True) ∧ (p2 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_16
          case intro assump_21 assump_22 =>
            apply False.elim assump_22
        case inr assump_18 =>
          cases assump_16
          case intro assump_29 assump_30 =>
            apply False.elim assump_30


variable (p3 p6 p2 p1 p7 p0 : Prop)
theorem file23_24238 : (((((p1 ∧ p1) ∧ (p3 ∧ True)) ∧ ((p3 ∧ p2) → (p6 ∨ p3))) ∧ (((p0 ∨ p7) → (p2 ∨ p2)) ∧ ((False → False) → False))) → False) := by
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
            cases assump_3
            case intro assump_22 assump_23 =>
              have assump_35 : (False → False) := by
                intro assump_29
                apply False.elim assump_29
              let assump_28 := assump_23 assump_35
              apply False.elim assump_28


variable (p5 p4 p2 p6 p0 p7 p1 p3 : Prop)
theorem file23_25039 : (((((p5 → p5) → False) → ((False → False) → False)) ∨ (((p3 ∨ False) → False) → False)) ∨ ((((p1 → False) ∨ (False ∨ p5)) ∧ ((p0 ∧ p3) → (p6 → p0))) ∨ (((True → True) → False) → ((p2 → p6) → (p4 ∧ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : (p5 → p5) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p3 p1 p4 p0 p5 p6 p2 : Prop)
theorem file23_25515 : (((((p2 ∧ p6) → (p1 → False)) → ((p1 → False) → (p0 → True))) → False) → ((((p6 ∧ p4) ∨ (p5 → p6)) ∧ ((p2 → p3) → (False ∨ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        have assump_37 : (((p2 ∧ p6) → (p1 → False)) → ((p1 → False) → (p0 → True))) := by
          intro assump_18
          intro assump_19
          intro assump_20
          apply True.intro
        let assump_17 := assump_1 assump_37
        apply False.elim assump_17
    case inr assump_6 =>
      have assump_38 : (((p2 ∧ p6) → (p1 → False)) → ((p1 → False) → (p0 → True))) := by
        intro assump_31
        intro assump_32
        intro assump_33
        apply True.intro
      let assump_30 := assump_1 assump_38
      apply False.elim assump_30


variable (p3 p7 p2 p5 : Prop)
theorem file23_26463 : ((((((p2 ∨ p7) → (False ∨ True)) ∨ ((p5 → False) ∨ (False ∨ p3))) ∨ (((p7 → False) ∨ (p5 ∨ True)) → ((p2 → False) → (p7 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∨ p7) → (False ∨ True)) ∨ ((p5 → False) ∨ (False ∨ p3))) ∨ (((p7 → False) ∨ (p5 ∨ True)) → ((p2 → False) → (p7 ∨ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p7 p1 p6 : Prop)
theorem file23_27116 : (((((False → p7) ∧ (p1 ∧ p5)) → False) ∧ (((False → False) → False) ∧ ((p6 → False) ∨ (False ∧ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_26 : (False → False) := by
          intro assump_16
          apply False.elim assump_16
        let assump_15 := assump_6 assump_26
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_22 assump_23 =>
          apply False.elim assump_22


variable (p0 p1 p3 p4 p5 : Prop)
theorem file23_27782 : ((((((p3 → False) ∨ (p3 ∧ True)) → ((p5 ∨ p3) → False)) → False) ∧ ((((p4 ∧ False) → False) ∨ ((p5 ∧ p0) → False)) → (((p3 → True) ∧ (p4 ∧ False)) ∧ ((p1 → True) → (False ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((p4 ∧ False) → False) ∨ ((p5 ∧ p0) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_24
    let assump_16 := And.left assump_8
    let assump_17 := And.right assump_16
    let assump_19 := And.right assump_17
    apply False.elim assump_19


variable (p7 p0 p2 p4 p6 p1 : Prop)
theorem file23_28510 : ((((((p1 ∧ p7) ∨ (p0 ∧ p6)) ∧ ((p0 ∧ True) ∨ (p2 → False))) → False) ∧ ((((p4 ∧ False) → (p4 ∨ False)) → ((False → p6) ∨ (p7 ∧ p4))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_26 : (((p4 ∧ False) → (p4 ∨ False)) → ((False → p6) ∨ (p7 ∧ p4))) := by
      intro assump_17
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_16 := assump_11 assump_26
    apply False.elim assump_16


variable (p5 p3 p6 p4 p0 p1 : Prop)
theorem file23_29054 : (((((p1 ∨ True) → (True → True)) → False) → False) ∨ ((((p1 ∧ p5) ∨ (p0 → p6)) ∧ ((p1 ∧ p4) → False)) → (((p6 → False) → False) ∨ ((p1 → True) → (p3 ∧ p6))))) := by
  apply Or.inl
  intro assump_26
  have assump_35 : ((p1 ∨ True) → (True → True)) := by
    intro assump_30
    intro assump_31
    apply True.intro
  let assump_29 := assump_26 assump_35
  apply False.elim assump_29


variable (p7 p3 p0 p5 : Prop)
theorem file23_29490 : (((((p3 ∧ p7) → (False ∨ True)) ∨ ((p5 → False) ∧ (p0 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p3 ∧ p7) → (False ∨ True)) ∨ ((p5 → False) ∧ (p0 ∧ p3))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p6 p1 p4 p0 p3 p7 p2 : Prop)
theorem file23_29942 : (((((p7 → p4) → (p1 → p4)) → False) → False) → ((((p4 → p6) ∨ (p6 → p4)) → ((p0 ∧ p3) → (p3 → p4))) → (((p7 ∨ False) ∧ (p5 ∧ p0)) → ((p1 ∨ p3) → (p2 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          apply Or.inr
          exact assump_16
      case inr assump_12 =>
        apply False.elim assump_12
  case inr assump_6 =>
    cases assump_3
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        cases assump_30
        case intro assump_35 assump_36 =>
          apply Or.inr
          exact assump_36
      case inr assump_32 =>
        apply False.elim assump_32


variable (p6 p1 p7 p2 p0 p4 p5 : Prop)
theorem file23_30869 : ((((((p4 ∧ p0) ∨ (False → p5)) → ((p1 → True) ∧ (p0 ∨ p6))) ∨ (((p7 → False) → (p4 → p2)) ∨ ((p0 → True) → False))) ∧ ((((False → p5) ∧ (p2 → p5)) → False) ∧ (((p7 → p7) ∨ (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_53 : ((p7 → p7) ∨ (p5 → False)) := by
          apply Or.inl
          intro assump_15
          exact assump_15
        let assump_14 := assump_9 assump_53
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        cases assump_3
        case intro assump_25 assump_26 =>
          have assump_54 : ((p7 → p7) ∨ (p5 → False)) := by
            apply Or.inl
            intro assump_32
            exact assump_32
          let assump_31 := assump_26 assump_54
          apply False.elim assump_31
      case inr assump_22 =>
        cases assump_3
        case intro assump_40 assump_41 =>
          have assump_55 : ((p7 → p7) ∨ (p5 → False)) := by
            apply Or.inl
            intro assump_47
            exact assump_47
          let assump_46 := assump_41 assump_55
          apply False.elim assump_46


variable (p5 p2 p6 p7 p3 p0 : Prop)
theorem file23_32206 : (((((False → False) ∨ (True → False)) → False) → False) ∨ ((((p6 ∨ p6) ∧ (False ∧ p0)) → False) ∨ (((p2 → False) ∨ (p7 ∨ p6)) → ((p3 ∨ False) ∧ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (True → False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p3 p7 p6 : Prop)
theorem file23_32650 : ((((((p3 → True) → (p0 ∧ p0)) → ((p0 ∧ True) ∧ (False → False))) ∧ (((False ∧ False) ∧ (p6 ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p3 → True) → (p0 ∧ p0)) → ((p0 ∧ True) ∧ (False → False))) ∧ (((False ∧ False) ∧ (p6 ∧ p7)) → False)) := by
    apply And.intro
    intro assump_5
    apply And.intro
    apply And.intro
    have assump_26 : (p3 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_26
    let assump_10 := And.left assump_8
    exact assump_10
    apply True.intro
    intro assump_12
    apply False.elim assump_12
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p4 : Prop)
theorem file23_33550 : ((((((p4 ∨ p0) → (p4 ∨ p0)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∨ p0) → (p4 ∨ p0)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p4 ∨ p0) → (p4 ∨ p0)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        exact assump_10
      case inr assump_11 =>
        apply Or.inr
        exact assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p2 p7 p4 : Prop)
theorem file23_34152 : (((((p3 ∧ p4) ∧ (p4 → False)) → ((p7 → p3) ∧ (False ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_36 : (((p3 ∧ p4) ∧ (p4 → False)) → ((p7 → p3) ∧ (False ∨ p2))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        exact assump_11
    cases assump_5
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        have assump_37 : p4 := by
          exact assump_22
        let assump_29 := assump_20 assump_37
        apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p4 p3 p6 p7 p0 p2 p1 : Prop)
theorem file23_34922 : ((((((p4 → p4) ∨ (p6 → p0)) ∨ ((p4 ∨ p3) ∨ (p0 ∧ p2))) ∨ (((p2 → p7) → (p6 ∨ p3)) ∨ ((p1 → True) ∧ (p7 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p4 → p4) ∨ (p6 → p0)) ∨ ((p4 ∨ p3) ∨ (p0 ∧ p2))) ∨ (((p2 → p7) → (p6 ∨ p3)) ∨ ((p1 → True) ∧ (p7 ∧ p4)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p6 p7 p0 p4 p1 p5 p2 : Prop)
theorem file23_35430 : (((((p4 ∧ p6) ∧ (p0 ∨ p4)) ∨ ((p2 → False) → (False ∨ p1))) ∧ (((p7 ∧ p1) → (p5 ∧ p0)) ∧ ((p5 ∧ False) ∧ (p6 ∧ False)))) → ((((p6 → False) ∨ (p6 → False)) ∨ ((p3 → False) → (p6 ∧ p2))) → (((p6 → p1) ∧ (True ∨ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      cases assump_2
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_1
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_23
                  case inl assump_30 =>
                    cases assump_19
                    case intro assump_34 assump_35 =>
                      cases assump_35
                      case intro assump_38 assump_39 =>
                        cases assump_38
                        case intro assump_40 assump_41 =>
                          apply False.elim assump_41
                  case inr assump_31 =>
                    cases assump_19
                    case intro assump_48 assump_49 =>
                      cases assump_49
                      case intro assump_52 assump_53 =>
                        cases assump_52
                        case intro assump_54 assump_55 =>
                          apply False.elim assump_55
            case inr assump_21 =>
              cases assump_19
              case intro assump_62 assump_63 =>
                cases assump_63
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case intro assump_68 assump_69 =>
                    apply False.elim assump_69
        case inr assump_15 =>
          cases assump_1
          case intro assump_76 assump_77 =>
            cases assump_76
            case inl assump_78 =>
              cases assump_78
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  cases assump_81
                  case inl assump_88 =>
                    cases assump_77
                    case intro assump_92 assump_93 =>
                      cases assump_93
                      case intro assump_96 assump_97 =>
                        cases assump_96
                        case intro assump_98 assump_99 =>
                          apply False.elim assump_99
                  case inr assump_89 =>
                    cases assump_77
                    case intro assump_106 assump_107 =>
                      cases assump_107
                      case intro assump_110 assump_111 =>
                        cases assump_110
                        case intro assump_112 assump_113 =>
                          apply False.elim assump_113
            case inr assump_79 =>
              cases assump_77
              case intro assump_120 assump_121 =>
                cases assump_121
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case intro assump_126 assump_127 =>
                    apply False.elim assump_127
      case inr assump_13 =>
        cases assump_1
        case intro assump_134 assump_135 =>
          cases assump_134
          case inl assump_136 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              cases assump_138
              case intro assump_140 assump_141 =>
                cases assump_139
                case inl assump_146 =>
                  cases assump_135
                  case intro assump_150 assump_151 =>
                    cases assump_151
                    case intro assump_154 assump_155 =>
                      cases assump_154
                      case intro assump_156 assump_157 =>
                        apply False.elim assump_157
                case inr assump_147 =>
                  cases assump_135
                  case intro assump_164 assump_165 =>
                    cases assump_165
                    case intro assump_168 assump_169 =>
                      cases assump_168
                      case intro assump_170 assump_171 =>
                        apply False.elim assump_171
          case inr assump_137 =>
            cases assump_135
            case intro assump_178 assump_179 =>
              cases assump_179
              case intro assump_182 assump_183 =>
                cases assump_182
                case intro assump_184 assump_185 =>
                  apply False.elim assump_185
    case inr assump_9 =>
      cases assump_2
      case inl assump_192 =>
        cases assump_192
        case inl assump_194 =>
          cases assump_1
          case intro assump_198 assump_199 =>
            cases assump_198
            case inl assump_200 =>
              cases assump_200
              case intro assump_202 assump_203 =>
                cases assump_202
                case intro assump_204 assump_205 =>
                  cases assump_203
                  case inl assump_210 =>
                    cases assump_199
                    case intro assump_214 assump_215 =>
                      cases assump_215
                      case intro assump_218 assump_219 =>
                        cases assump_218
                        case intro assump_220 assump_221 =>
                          apply False.elim assump_221
                  case inr assump_211 =>
                    cases assump_199
                    case intro assump_228 assump_229 =>
                      cases assump_229
                      case intro assump_232 assump_233 =>
                        cases assump_232
                        case intro assump_234 assump_235 =>
                          apply False.elim assump_235
            case inr assump_201 =>
              cases assump_199
              case intro assump_242 assump_243 =>
                cases assump_243
                case intro assump_246 assump_247 =>
                  cases assump_246
                  case intro assump_248 assump_249 =>
                    apply False.elim assump_249
        case inr assump_195 =>
          cases assump_1
          case intro assump_256 assump_257 =>
            cases assump_256
            case inl assump_258 =>
              cases assump_258
              case intro assump_260 assump_261 =>
                cases assump_260
                case intro assump_262 assump_263 =>
                  cases assump_261
                  case inl assump_268 =>
                    cases assump_257
                    case intro assump_272 assump_273 =>
                      cases assump_273
                      case intro assump_276 assump_277 =>
                        cases assump_276
                        case intro assump_278 assump_279 =>
                          apply False.elim assump_279
                  case inr assump_269 =>
                    cases assump_257
                    case intro assump_286 assump_287 =>
                      cases assump_287
                      case intro assump_290 assump_291 =>
                        cases assump_290
                        case intro assump_292 assump_293 =>
                          apply False.elim assump_293
            case inr assump_259 =>
              cases assump_257
              case intro assump_300 assump_301 =>
                cases assump_301
                case intro assump_304 assump_305 =>
                  cases assump_304
                  case intro assump_306 assump_307 =>
                    apply False.elim assump_307
      case inr assump_193 =>
        cases assump_1
        case intro assump_314 assump_315 =>
          cases assump_314
          case inl assump_316 =>
            cases assump_316
            case intro assump_318 assump_319 =>
              cases assump_318
              case intro assump_320 assump_321 =>
                cases assump_319
                case inl assump_326 =>
                  cases assump_315
                  case intro assump_330 assump_331 =>
                    cases assump_331
                    case intro assump_334 assump_335 =>
                      cases assump_334
                      case intro assump_336 assump_337 =>
                        apply False.elim assump_337
                case inr assump_327 =>
                  cases assump_315
                  case intro assump_344 assump_345 =>
                    cases assump_345
                    case intro assump_348 assump_349 =>
                      cases assump_348
                      case intro assump_350 assump_351 =>
                        apply False.elim assump_351
          case inr assump_317 =>
            cases assump_315
            case intro assump_358 assump_359 =>
              cases assump_359
              case intro assump_362 assump_363 =>
                cases assump_362
                case intro assump_364 assump_365 =>
                  apply False.elim assump_365


variable (p2 p1 p6 p0 p7 p4 p3 : Prop)
theorem file23_44696 : (((((p2 ∧ p7) ∨ (p0 ∨ p0)) ∧ ((p7 ∧ p3) ∨ (p4 ∧ p1))) → (((True → False) → False) → ((p6 ∧ p6) → (p3 ∨ p1)))) ∨ ((((p2 → p7) → False) → False) → False)) := by
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
        case intro assump_16 assump_17 =>
          cases assump_13
          case inl assump_22 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply Or.inl
              exact assump_25
          case inr assump_23 =>
            cases assump_23
            case intro assump_30 assump_31 =>
              apply Or.inr
              exact assump_31
      case inr assump_15 =>
        cases assump_15
        case inl assump_36 =>
          cases assump_13
          case inl assump_40 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              apply Or.inl
              exact assump_43
          case inr assump_41 =>
            cases assump_41
            case intro assump_48 assump_49 =>
              apply Or.inr
              exact assump_49
        case inr assump_37 =>
          cases assump_13
          case inl assump_56 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              apply Or.inl
              exact assump_59
          case inr assump_57 =>
            cases assump_57
            case intro assump_64 assump_65 =>
              apply Or.inr
              exact assump_65


variable (p1 p0 p3 p5 p2 p6 p7 : Prop)
theorem file23_46376 : (((((p6 → False) → False) → ((True → p3) ∧ (p6 ∧ False))) ∧ (((p5 → False) ∧ (p1 ∨ False)) → ((p5 ∧ p2) → (p7 ∨ p1)))) → ((((p5 ∧ p6) ∨ (True ∨ p0)) ∧ ((p3 ∨ p7) → (p2 → p2))) ∨ (((p0 ∧ p0) ∨ (True ∧ p3)) → False))) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    apply Or.inl
    apply And.intro
    apply Or.inr
    apply Or.inl
    apply True.intro
    intro assump_20
    intro assump_21
    cases assump_20
    case inl assump_24 =>
      exact assump_21
    case inr assump_25 =>
      exact assump_21


variable (p2 p7 p5 p6 p0 p1 p3 p4 : Prop)
theorem file23_46984 : ((((((p0 → True) → False) ∧ ((False ∧ False) → False)) ∧ (((p7 ∧ p6) ∨ (p2 → False)) ∧ ((p2 → False) ∧ (True ∧ p0)))) ∧ ((((p6 → False) ∧ (p3 → p5)) ∨ ((p2 ∨ False) → (p6 ∨ p6))) ∨ (((p5 ∨ p4) → (p1 → False)) ∧ ((p1 ∧ p7) ∨ (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_13
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_3
                  case inl assump_32 =>
                    cases assump_32
                    case inl assump_34 =>
                      cases assump_34
                      case intro assump_36 assump_37 =>
                        have assump_173 : p6 := by
                          exact assump_17
                        let assump_43 := assump_36 assump_173
                        apply False.elim assump_43
                    case inr assump_35 =>
                      have assump_174 : (p0 → True) := by
                        intro assump_56
                        apply True.intro
                      let assump_55 := assump_6 assump_174
                      apply False.elim assump_55
                  case inr assump_33 =>
                    cases assump_33
                    case intro assump_60 assump_61 =>
                      cases assump_61
                      case inl assump_64 =>
                        cases assump_64
                        case intro assump_66 assump_67 =>
                          have assump_175 : (p0 → True) := by
                            intro assump_81
                            apply True.intro
                          let assump_80 := assump_6 assump_175
                          apply False.elim assump_80
                      case inr assump_65 =>
                        have assump_176 : p6 := by
                          exact assump_17
                        let assump_87 := assump_65 assump_176
                        apply False.elim assump_87
          case inr assump_15 =>
            cases assump_13
            case intro assump_93 assump_94 =>
              cases assump_94
              case intro assump_97 assump_98 =>
                cases assump_3
                case inl assump_103 =>
                  cases assump_103
                  case inl assump_105 =>
                    cases assump_105
                    case intro assump_107 assump_108 =>
                      have assump_177 : (p0 → True) := by
                        intro assump_120
                        apply True.intro
                      let assump_119 := assump_6 assump_177
                      apply False.elim assump_119
                  case inr assump_106 =>
                    have assump_178 : (p0 → True) := by
                      intro assump_132
                      apply True.intro
                    let assump_131 := assump_6 assump_178
                    apply False.elim assump_131
                case inr assump_104 =>
                  cases assump_104
                  case intro assump_136 assump_137 =>
                    cases assump_137
                    case inl assump_140 =>
                      cases assump_140
                      case intro assump_142 assump_143 =>
                        have assump_179 : (p0 → True) := by
                          intro assump_156
                          apply True.intro
                        let assump_155 := assump_6 assump_179
                        apply False.elim assump_155
                    case inr assump_141 =>
                      have assump_180 : (p0 → True) := by
                        intro assump_169
                        apply True.intro
                      let assump_168 := assump_6 assump_180
                      apply False.elim assump_168


variable (p2 p4 p3 p5 p0 p7 p6 : Prop)
theorem file23_51221 : ((((((p2 → p6) → (p4 ∧ p0)) → False) ∨ (((p4 → p4) ∧ (p6 ∧ p7)) ∧ ((p0 → False) ∧ (p4 ∧ p7)))) ∧ ((((p5 ∨ p6) → (True → False)) ∧ ((True ∧ p7) → (p5 → False))) ∧ (((p7 ∧ False) → (p3 ∨ p0)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_9
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_78 : ((p7 ∧ False) → (p3 ∨ p0)) := by
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
          let assump_24 := assump_15 assump_78
          apply False.elim assump_24
    case inr assump_11 =>
      cases assump_11
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            cases assump_36
            case intro assump_47 assump_48 =>
              cases assump_48
              case intro assump_51 assump_52 =>
                cases assump_9
                case intro assump_57 assump_58 =>
                  cases assump_57
                  case intro assump_59 assump_60 =>
                    have assump_79 : ((p7 ∧ False) → (p3 ∨ p0)) := by
                      intro assump_68
                      cases assump_68
                      case intro assump_69 assump_70 =>
                        apply False.elim assump_70
                    let assump_67 := assump_58 assump_79
                    apply False.elim assump_67


variable (p4 p5 p6 : Prop)
theorem file23_52915 : ((((((p6 → False) → (p5 ∨ True)) → False) → False) ∧ ((((p5 → False) → (True ∧ True)) ∧ ((False ∧ p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p5 → False) → (True ∧ True)) ∧ ((False ∧ p4) → False)) := by
      apply And.intro
      intro assump_9
      apply And.intro
      apply True.intro
      apply True.intro
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p0 p7 p5 p4 p2 : Prop)
theorem file23_53561 : (((((p2 ∨ p4) → (False → p5)) → False) ∧ (((p0 ∧ p2) ∧ (True → False)) ∧ ((p7 ∧ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_25 : True := by
            apply True.intro
          let assump_21 := assump_9 assump_25
          apply False.elim assump_21


variable (p2 p0 p5 p7 : Prop)
theorem file23_54122 : ((((((p2 → False) ∨ (p0 → False)) → False) → (((True ∧ False) ∧ (p7 ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → False) ∨ (p0 → False)) → False) → (((True ∧ False) ∧ (p7 ∧ p5)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p5 p1 p2 p4 p3 : Prop)
theorem file23_54669 : (((((True ∨ p1) → False) ∧ ((True → p7) ∨ (p1 → False))) → False) ∨ ((((p4 → True) → False) ∧ ((p3 → False) → False)) ∨ (((p5 ∧ p1) → (p4 → False)) ∧ ((p5 → False) ∨ (p7 → p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_23 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_2 assump_23
      apply False.elim assump_12
    case inr assump_7 =>
      have assump_24 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_19 := assump_2 assump_24
      apply False.elim assump_19


variable (p3 p6 p4 p5 p7 p2 p0 p1 : Prop)
theorem file23_55397 : (((((p6 ∧ p1) → (True → False)) → False) → (((False ∧ p4) → False) ∨ ((p1 ∨ True) → False))) → ((((p4 ∨ p0) ∧ (p2 → p5)) ∨ ((p0 ∨ p5) ∨ (p3 ∨ p3))) ∨ (((p2 → True) → (False → False)) ∨ ((False ∧ p2) → (p7 → p1))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p5 p6 p1 p0 : Prop)
theorem file23_55781 : ((((((p1 ∧ p0) ∨ (False ∨ p0)) → False) → False) ∧ ((((True → False) ∧ (p5 → p6)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_24 : (((True → False) ∧ (p5 → p6)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        have assump_25 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_25
        apply False.elim assump_17
    let assump_8 := assump_3 assump_24
    apply False.elim assump_8


variable (p6 p7 p3 p2 p5 p4 p1 : Prop)
theorem file23_56388 : ((((((p7 → False) → False) ∨ ((True ∧ p5) → (p4 ∧ p6))) → False) ∧ ((((p1 → p3) ∧ (p2 → p3)) → ((p2 ∧ True) → (p6 ∨ True))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_36 : (((p1 → p3) ∧ (p2 → p3)) → ((p2 ∧ True) → (p6 ∨ True))) := by
      intro assump_19
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        cases assump_19
        case intro assump_27 assump_28 =>
          apply Or.inr
          apply True.intro
    let assump_18 := assump_13 assump_36
    apply False.elim assump_18


variable (p1 p2 p7 p3 : Prop)
theorem file23_57040 : (((((p2 ∧ p7) ∨ (p2 ∨ p3)) → ((p1 ∧ True) → (True ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_30 : (((p2 ∧ p7) ∨ (p2 ∨ p3)) → ((p1 ∧ True) → (True ∨ p7))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply True.intro
      case inr assump_14 =>
        cases assump_14
        case inl assump_21 =>
          apply Or.inl
          apply True.intro
        case inr assump_22 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p3 : Prop)
theorem file23_57803 : ((((((False → p2) → False) ∨ ((True → False) ∨ (p3 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_34 : ((((False → p2) → False) ∨ ((True → False) ∨ (p3 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      have assump_35 : (False → p2) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_6 assump_35
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case inl assump_17 =>
        have assump_36 : True := by
          apply True.intro
        let assump_21 := assump_17 assump_36
        apply False.elim assump_21
      case inr assump_18 =>
        cases assump_18
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p3 p1 p7 p2 p4 p0 p6 p5 : Prop)
theorem file23_58727 : (((((p5 → p7) ∧ (p6 ∧ False)) ∧ ((p4 ∨ p4) ∧ (True ∨ p5))) → (((p5 ∨ p7) → False) ∨ ((p2 ∧ p2) ∧ (p2 ∨ p5)))) ∨ ((((p3 ∧ p0) → (p1 ∧ p3)) ∨ ((p6 ∨ p6) → False)) ∧ (((p0 ∧ p4) → False) ∨ ((p1 ∨ True) → (p2 → p2))))) := by
  apply Or.inl
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_44
    case intro assump_46 assump_47 =>
      cases assump_47
      case intro assump_50 assump_51 =>
        apply False.elim assump_51


variable (p3 p4 p2 p5 : Prop)
theorem file23_59244 : ((((((p5 ∧ p4) ∨ (False ∧ p3)) ∧ ((p2 ∨ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p5 ∧ p4) ∨ (False ∧ p3)) ∧ ((p2 ∨ p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_30 : (p2 ∨ p4) := by
            apply Or.inr
            exact assump_11
          let assump_18 := assump_7 assump_30
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p4 p6 p2 p1 p7 p5 p0 : Prop)
theorem file23_60057 : (((((p1 → p0) → (p7 → False)) ∨ ((p4 → False) ∧ (p5 ∧ p6))) ∧ (((p1 → p1) → False) ∧ ((p0 ∨ p5) → False))) → ((((True → False) ∧ (p2 → False)) → ((False ∨ p4) → (p2 → False))) ∨ (((p2 ∨ False) → False) → ((p6 → p5) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        intro assump_15
        intro assump_16
        cases assump_15
        case inl assump_19 =>
          apply False.elim assump_19
        case inr assump_20 =>
          cases assump_14
          case intro assump_25 assump_26 =>
            have assump_72 : p2 := by
              exact assump_16
            let assump_31 := assump_26 assump_72
            apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case intro assump_35 assump_36 =>
        cases assump_36
        case intro assump_39 assump_40 =>
          cases assump_3
          case intro assump_45 assump_46 =>
            apply Or.inl
            intro assump_51
            intro assump_52
            intro assump_53
            cases assump_52
            case inl assump_56 =>
              apply False.elim assump_56
            case inr assump_57 =>
              cases assump_51
              case intro assump_62 assump_63 =>
                have assump_73 : p2 := by
                  exact assump_53
                let assump_68 := assump_63 assump_73
                apply False.elim assump_68


variable (p0 p4 p3 p5 p1 p2 p7 p6 : Prop)
theorem file23_61684 : ((((((p7 ∨ p5) ∧ (p6 ∨ False)) → ((p3 → p4) → (p1 → False))) → False) ∧ ((((p0 → False) ∨ (p0 ∨ p4)) ∧ ((p5 ∨ p0) ∧ (False ∧ p0))) ∧ (((p6 ∧ p3) → False) → ((p2 ∧ p7) ∨ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
            case inr assump_17 =>
              cases assump_15
              case intro assump_26 assump_27 =>
                apply False.elim assump_26
        case inr assump_11 =>
          cases assump_11
          case inl assump_30 =>
            cases assump_9
            case intro assump_34 assump_35 =>
              cases assump_34
              case inl assump_36 =>
                cases assump_35
                case intro assump_40 assump_41 =>
                  apply False.elim assump_40
              case inr assump_37 =>
                cases assump_35
                case intro assump_46 assump_47 =>
                  apply False.elim assump_46
          case inr assump_31 =>
            cases assump_9
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                cases assump_53
                case intro assump_58 assump_59 =>
                  apply False.elim assump_58
              case inr assump_55 =>
                cases assump_53
                case intro assump_64 assump_65 =>
                  apply False.elim assump_64


variable (p5 p4 p7 p3 p1 p6 p2 : Prop)
theorem file23_63571 : ((((((p4 ∨ False) → False) ∧ ((p7 ∧ False) ∧ (True ∧ False))) → (((p6 → False) → False) → ((p5 ∨ p2) → (p1 → p3)))) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p4 ∨ False) → False) ∧ ((p7 ∧ False) ∧ (True ∧ False))) → (((p6 → False) → False) → ((p5 ∨ p2) → (p1 → p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply False.elim assump_24
    case inr assump_12 =>
      cases assump_5
      case intro assump_33 assump_34 =>
        cases assump_34
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            apply False.elim assump_40
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p6 p2 p4 p5 p0 p3 p7 : Prop)
theorem file23_64614 : (((((p0 ∧ p3) ∨ (p6 ∧ p6)) ∨ ((p6 ∨ p7) → (p6 ∧ False))) → False) → ((((p7 ∨ p2) ∨ (p6 → False)) → ((p5 ∨ True) ∨ (False → False))) ∨ (((p4 ∧ p7) ∧ (p4 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p4 p1 p6 p0 : Prop)
theorem file23_65205 : (((((p6 ∨ p4) ∨ (p1 → p0)) → ((True → False) → False)) → False) → False) := by
  intro assump_5
  have assump_41 : (((p6 ∨ p4) ∨ (p1 → p0)) → ((True → False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_9
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        have assump_42 : True := by
          apply True.intro
        let assump_20 := assump_10 assump_42
        apply False.elim assump_20
      case inr assump_16 =>
        have assump_43 : True := by
          apply True.intro
        let assump_27 := assump_10 assump_43
        apply False.elim assump_27
    case inr assump_14 =>
      have assump_44 : True := by
        apply True.intro
      let assump_34 := assump_10 assump_44
      apply False.elim assump_34
  let assump_8 := assump_5 assump_41
  apply False.elim assump_8


variable (p6 p4 p2 p1 p3 p5 p7 p0 : Prop)
theorem file23_66119 : (((((p1 → False) ∨ (p4 → False)) → ((p3 → False) → (p7 ∨ True))) ∨ (((False → p5) → (p5 → True)) ∨ ((False → False) ∧ (False → False)))) ∧ ((((p1 ∧ p0) → False) ∧ ((p2 → p0) ∨ (p6 → False))) → (((p7 ∨ False) ∧ (p6 → p2)) → ((p5 → p6) → (p6 ∨ p7))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    apply Or.inr
    apply True.intro
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    cases assump_16
    case inl assump_18 =>
      cases assump_11
      case intro assump_24 assump_25 =>
        cases assump_25
        case inl assump_28 =>
          apply Or.inr
          exact assump_18
        case inr assump_29 =>
          apply Or.inr
          exact assump_18
    case inr assump_19 =>
      apply False.elim assump_19


variable (p5 p4 p2 p6 p3 : Prop)
theorem file23_67095 : ((((((True → p4) ∨ (p4 → p6)) ∧ ((p5 ∨ p5) ∧ (p2 ∨ p6))) → (((p5 → False) → False) ∨ ((p6 → False) → (p3 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_113 : ((((True → p4) ∨ (p4 → p6)) ∧ ((p5 ∨ p5) ∧ (p2 ∨ p6))) → (((p5 → False) → False) ∨ ((p6 → False) → (p3 ∧ p3)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case inl assump_18 =>
              apply Or.inl
              intro assump_22
              have assump_114 : p5 := by
                exact assump_14
              let assump_25 := assump_22 assump_114
              apply False.elim assump_25
            case inr assump_19 =>
              apply Or.inl
              intro assump_31
              have assump_115 : p5 := by
                exact assump_14
              let assump_34 := assump_31 assump_115
              apply False.elim assump_34
          case inr assump_15 =>
            cases assump_13
            case inl assump_40 =>
              apply Or.inl
              intro assump_44
              have assump_116 : p5 := by
                exact assump_15
              let assump_47 := assump_44 assump_116
              apply False.elim assump_47
            case inr assump_41 =>
              apply Or.inl
              intro assump_53
              have assump_117 : p5 := by
                exact assump_15
              let assump_56 := assump_53 assump_117
              apply False.elim assump_56
      case inr assump_9 =>
        cases assump_7
        case intro assump_62 assump_63 =>
          cases assump_62
          case inl assump_64 =>
            cases assump_63
            case inl assump_68 =>
              apply Or.inl
              intro assump_72
              have assump_118 : p5 := by
                exact assump_64
              let assump_75 := assump_72 assump_118
              apply False.elim assump_75
            case inr assump_69 =>
              apply Or.inl
              intro assump_81
              have assump_119 : p5 := by
                exact assump_64
              let assump_84 := assump_81 assump_119
              apply False.elim assump_84
          case inr assump_65 =>
            cases assump_63
            case inl assump_90 =>
              apply Or.inl
              intro assump_94
              have assump_120 : p5 := by
                exact assump_65
              let assump_97 := assump_94 assump_120
              apply False.elim assump_97
            case inr assump_91 =>
              apply Or.inl
              intro assump_103
              have assump_121 : p5 := by
                exact assump_65
              let assump_106 := assump_103 assump_121
              apply False.elim assump_106
  let assump_4 := assump_1 assump_113
  apply False.elim assump_4


variable (p5 p0 p1 p3 p7 : Prop)
theorem file23_70142 : (((((p0 ∨ True) ∧ (False → p7)) → ((p1 ∨ True) → (False ∧ p5))) → False) → ((((True ∨ p3) → (p5 → p1)) → False) → (((p1 → False) ∧ (False ∧ p3)) → False))) := by
  intro assump_8
  intro assump_9
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      apply False.elim assump_15


variable (p2 p6 p5 p7 p3 p0 p1 p4 : Prop)
theorem file23_70567 : (((((p0 ∧ p2) ∧ (p3 ∧ p2)) ∧ ((p3 ∧ p7) ∨ (p3 ∧ p1))) ∨ (((p7 ∧ p0) ∨ (p2 ∨ p2)) ∧ ((p0 → False) ∧ (False → p5)))) → ((((p1 → p2) → False) → False) ∧ (((False ∨ p2) ∨ (p4 ∨ p6)) ∨ ((False → p2) → False)))) := by
  intro assump_11
  apply And.intro
  intro assump_12
  cases assump_11
  case inl assump_15 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_20
          case intro assump_27 assump_28 =>
            cases assump_18
            case inl assump_33 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                have assump_207 : (p1 → p2) := by
                  intro assump_48
                  exact assump_28
                let assump_47 := assump_12 assump_207
                apply False.elim assump_47
            case inr assump_34 =>
              cases assump_34
              case intro assump_54 assump_55 =>
                have assump_208 : (p1 → p2) := by
                  intro assump_67
                  exact assump_28
                let assump_66 := assump_12 assump_208
                apply False.elim assump_66
  case inr assump_16 =>
    cases assump_16
    case intro assump_73 assump_74 =>
      cases assump_73
      case inl assump_75 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          cases assump_74
          case intro assump_83 assump_84 =>
            have assump_209 : p0 := by
              exact assump_78
            let assump_90 := assump_83 assump_209
            apply False.elim assump_90
      case inr assump_76 =>
        cases assump_76
        case inl assump_94 =>
          cases assump_74
          case intro assump_98 assump_99 =>
            have assump_210 : (p1 → p2) := by
              intro assump_108
              exact assump_94
            let assump_107 := assump_12 assump_210
            apply False.elim assump_107
        case inr assump_95 =>
          cases assump_74
          case intro assump_116 assump_117 =>
            have assump_211 : (p1 → p2) := by
              intro assump_126
              exact assump_95
            let assump_125 := assump_12 assump_211
            apply False.elim assump_125
  cases assump_11
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
            case inl assump_150 =>
              cases assump_150
              case intro assump_152 assump_153 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_145
            case inr assump_151 =>
              cases assump_151
              case intro assump_158 assump_159 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_145
  case inr assump_133 =>
    cases assump_133
    case intro assump_164 assump_165 =>
      cases assump_164
      case inl assump_166 =>
        cases assump_166
        case intro assump_168 assump_169 =>
          cases assump_165
          case intro assump_174 assump_175 =>
            apply Or.inr
            intro assump_180
            have assump_212 : p0 := by
              exact assump_169
            let assump_185 := assump_174 assump_212
            apply False.elim assump_185
      case inr assump_167 =>
        cases assump_167
        case inl assump_189 =>
          cases assump_165
          case intro assump_193 assump_194 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_189
        case inr assump_190 =>
          cases assump_165
          case intro assump_201 assump_202 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_190


variable (p4 p3 p2 p5 p0 p7 p1 : Prop)
theorem file23_74730 : (((((True → False) → (p3 → p2)) ∨ ((p1 → False) ∨ (p0 → p5))) ∨ (((False → False) → (p4 → False)) ∧ ((False → False) → False))) ∨ ((((p7 ∨ p5) ∧ (False → False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_5 assump_15
  apply False.elim assump_11


variable (p0 p3 p5 p6 p1 p4 : Prop)
theorem file23_75174 : ((((((p0 → p5) ∧ (p0 ∨ p4)) ∨ ((p4 → False) → False)) → (((p4 ∧ p4) → (True → p6)) → ((p3 → True) ∨ (False ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 → p5) ∧ (p0 ∨ p4)) ∨ ((p4 → False) → False)) → (((p4 ∧ p4) → (True → p6)) → ((p3 → True) ∨ (False ∨ p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          apply Or.inl
          intro assump_19
          apply True.intro
        case inr assump_16 =>
          apply Or.inl
          intro assump_22
          apply True.intro
    case inr assump_10 =>
      apply Or.inl
      intro assump_25
      apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p4 p1 p3 p0 p6 p5 p2 : Prop)
theorem file23_76067 : (((((True → False) ∧ (True → False)) → ((p6 ∨ p2) ∧ (p0 ∧ p5))) ∨ (((p1 ∨ True) → False) → False)) ∨ ((((p0 ∧ p4) → False) → ((True → p2) ∧ (p6 ∨ False))) ∨ (((p5 ∧ p3) ∨ (p4 ∧ p2)) ∨ ((True ∨ True) ∨ (False ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : True := by
      apply True.intro
    let assump_8 := assump_3 assump_32
    apply False.elim assump_8
  apply And.intro
  cases assump_1
  case intro assump_12 assump_13 =>
    have assump_33 : True := by
      apply True.intro
    let assump_18 := assump_13 assump_33
    apply False.elim assump_18
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_34 : True := by
      apply True.intro
    let assump_28 := assump_23 assump_34
    apply False.elim assump_28


variable (p6 p7 p5 p1 p0 p3 p4 p2 : Prop)
theorem file23_76975 : (((((p6 ∧ p1) ∨ (p0 → False)) → ((p2 ∧ False) ∧ (p3 ∨ True))) ∧ (((p5 → p5) → (p4 ∧ True)) → ((p3 ∨ p1) → (p4 → False)))) → ((((p7 → False) ∧ (p7 ∧ False)) → ((False → False) ∨ (p3 ∧ p0))) ∨ (((p1 ∧ p5) ∨ (p4 → True)) ∨ ((p3 ∧ p0) ∨ (p2 ∨ p2))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_14


variable (p6 p2 p0 p4 p1 p7 p3 : Prop)
theorem file23_77548 : (((((p7 → False) ∧ (p1 ∧ False)) → ((p4 → False) → (True ∧ p2))) ∨ (((p0 ∧ p1) ∨ (p6 ∧ p7)) → ((p3 ∧ True) ∨ (p1 → False)))) ∨ ((((True ∧ True) → False) ∨ ((p7 ∨ p4) ∨ (True ∨ p7))) ∨ (((p2 → False) → (p6 → p2)) ∧ ((p6 ∨ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_28
  intro assump_29
  apply And.intro
  apply True.intro
  cases assump_28
  case intro assump_32 assump_33 =>
    cases assump_33
    case intro assump_36 assump_37 =>
      apply False.elim assump_37


variable (p0 p5 p4 p2 p6 p3 p1 p7 : Prop)
theorem file23_78105 : (((((p1 → p2) → False) ∧ ((p0 ∨ p3) ∧ (p1 → False))) ∧ (((p5 → False) → (p3 → False)) → ((p0 → p7) ∨ (p7 ∨ p7)))) → ((((False ∧ p7) ∨ (p5 ∨ p0)) ∧ ((p3 ∧ False) → False)) → (((p4 ∧ p7) → (p4 ∨ p2)) ∨ ((p6 → False) → (p6 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
    case inr assump_6 =>
      cases assump_6
      case inl assump_11 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                apply Or.inl
                intro assump_33
                cases assump_33
                case intro assump_34 assump_35 =>
                  apply Or.inl
                  exact assump_34
              case inr assump_26 =>
                apply Or.inl
                intro assump_46
                cases assump_46
                case intro assump_47 assump_48 =>
                  apply Or.inl
                  exact assump_47
      case inr assump_12 =>
        cases assump_1
        case intro assump_57 assump_58 =>
          cases assump_57
          case intro assump_59 assump_60 =>
            cases assump_60
            case intro assump_63 assump_64 =>
              cases assump_63
              case inl assump_65 =>
                apply Or.inl
                intro assump_73
                cases assump_73
                case intro assump_74 assump_75 =>
                  apply Or.inl
                  exact assump_74
              case inr assump_66 =>
                apply Or.inl
                intro assump_86
                cases assump_86
                case intro assump_87 assump_88 =>
                  apply Or.inl
                  exact assump_87


variable (p7 p1 p0 p5 p6 p2 p3 : Prop)
theorem file23_80185 : ((((((p7 ∧ p3) ∨ (p1 → p3)) ∧ ((p6 ∧ p5) ∧ (p3 ∧ p2))) ∧ (((p0 ∧ p1) → False) → False)) ∧ ((((p0 → False) ∧ (p0 ∧ p2)) → ((p1 → True) ∧ (p5 ∨ False))) → False)) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case inl assump_24 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_23
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_33
                case intro assump_40 assump_41 =>
                  have assump_102 : (((p0 → False) ∧ (p0 ∧ p2)) → ((p1 → True) ∧ (p5 ∨ False))) := by
                    intro assump_51
                    apply And.intro
                    intro assump_52
                    apply True.intro
                    cases assump_51
                    case intro assump_53 assump_54 =>
                      cases assump_54
                      case intro assump_57 assump_58 =>
                        apply Or.inl
                        exact assump_35
                  let assump_50 := assump_19 assump_102
                  apply False.elim assump_50
        case inr assump_25 =>
          cases assump_23
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_69
              case intro assump_76 assump_77 =>
                have assump_103 : (((p0 → False) ∧ (p0 ∧ p2)) → ((p1 → True) ∧ (p5 ∨ False))) := by
                  intro assump_87
                  apply And.intro
                  intro assump_88
                  apply True.intro
                  cases assump_87
                  case intro assump_89 assump_90 =>
                    cases assump_90
                    case intro assump_93 assump_94 =>
                      apply Or.inl
                      exact assump_71
                let assump_86 := assump_19 assump_103
                apply False.elim assump_86


variable (p5 p2 p7 p0 p1 p4 p3 : Prop)
theorem file23_82418 : ((((((p3 ∧ p5) → False) ∧ ((p3 ∧ p2) ∧ (p1 ∨ False))) ∧ (((p0 → p5) → (p3 ∨ p7)) → ((p7 ∨ False) ∨ (p1 → p7)))) ∧ ((((p2 ∨ p1) → False) → ((p4 → False) ∨ (p5 → False))) → (((p1 → False) ∧ (False ∧ p1)) ∧ ((p5 ∧ p2) ∨ (False → p7))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case inl assump_22 =>
              have assump_50 : (((p2 ∨ p1) → False) → ((p4 → False) ∨ (p5 → False))) := by
                intro assump_31
                apply Or.inl
                intro assump_34
                have assump_51 : (p2 ∨ p1) := by
                  apply Or.inl
                  exact assump_17
                let assump_38 := assump_31 assump_51
                apply False.elim assump_38
              let assump_30 := assump_7 assump_50
              let assump_42 := And.left assump_30
              let assump_43 := And.left assump_42
              have assump_52 : p1 := by
                exact assump_22
              let assump_44 := assump_43 assump_52
              apply False.elim assump_44
            case inr assump_23 =>
              apply False.elim assump_23


variable (p1 p6 p0 p3 p7 p4 : Prop)
theorem file23_83892 : (((((True ∧ True) ∨ (p6 ∨ p3)) → False) → False) ∨ ((((True ∨ p4) → False) ∧ ((False ∨ p1) → False)) ∧ (((p6 ∧ p3) ∧ (p6 → p0)) → ((p0 ∨ p7) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∧ True) ∨ (p6 ∨ p3)) := by
    apply Or.inl
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p2 p4 p1 p7 p0 : Prop)
theorem file23_84338 : (((((p6 ∨ True) ∨ (True → False)) → False) ∧ (((p2 → p0) ∨ (False → p4)) ∨ ((p0 → False) ∧ (p4 → p7)))) → ((((p1 ∧ True) ∧ (p6 → p6)) ∨ ((p2 → False) ∧ (False → p0))) → False)) := by
  intro assump_10
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_10
        case intro assump_24 assump_25 =>
          cases assump_25
          case inl assump_28 =>
            cases assump_28
            case inl assump_30 =>
              have assump_98 : ((p6 ∨ True) ∨ (True → False)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_35 := assump_24 assump_98
              apply False.elim assump_35
            case inr assump_31 =>
              have assump_99 : ((p6 ∨ True) ∨ (True → False)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_42 := assump_24 assump_99
              apply False.elim assump_42
          case inr assump_29 =>
            cases assump_29
            case intro assump_46 assump_47 =>
              have assump_100 : ((p6 ∨ True) ∨ (True → False)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_54 := assump_24 assump_100
              apply False.elim assump_54
  case inr assump_13 =>
    cases assump_13
    case intro assump_58 assump_59 =>
      cases assump_10
      case intro assump_64 assump_65 =>
        cases assump_65
        case inl assump_68 =>
          cases assump_68
          case inl assump_70 =>
            have assump_101 : ((p6 ∨ True) ∨ (True → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_75 := assump_64 assump_101
            apply False.elim assump_75
          case inr assump_71 =>
            have assump_102 : ((p6 ∨ True) ∨ (True → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_82 := assump_64 assump_102
            apply False.elim assump_82
        case inr assump_69 =>
          cases assump_69
          case intro assump_86 assump_87 =>
            have assump_103 : ((p6 ∨ True) ∨ (True → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_94 := assump_64 assump_103
            apply False.elim assump_94


variable (p7 p6 p4 p5 p3 p2 p1 : Prop)
theorem file23_86974 : ((((((p3 → False) ∧ (True → p1)) ∨ ((p7 → False) → (p3 → True))) ∧ (((p7 → p2) ∧ (False ∧ True)) ∧ ((p2 ∧ p7) → False))) ∨ ((((p3 ∧ p7) ∧ (p6 ∧ False)) ∧ ((p7 ∨ p4) → (p6 ∨ True))) ∧ (((p3 ∨ p4) ∧ (p3 ∨ p6)) ∨ ((p5 → False) ∧ (p7 ∨ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
      case inr assump_7 =>
        cases assump_5
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_29
            case intro assump_32 assump_33 =>
              apply False.elim assump_32
  case inr assump_3 =>
    cases assump_3
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_41
            case intro assump_48 assump_49 =>
              apply False.elim assump_49


variable (p6 p3 p7 p0 p4 p1 : Prop)
theorem file23_88446 : ((((((p3 ∧ False) → (p1 → p4)) ∨ ((p4 ∨ p7) → False)) ∧ (((p6 → p6) ∧ (False → p0)) ∨ ((p6 ∨ False) ∧ (p4 → p4)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p3 ∧ False) → (p1 → p4)) ∨ ((p4 ∨ p7) → False)) ∧ (((p6 → p6) ∧ (False → p0)) ∨ ((p6 ∨ False) ∧ (p4 → p4)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
    apply Or.inl
    apply And.intro
    intro assump_15
    exact assump_15
    intro assump_18
    apply False.elim assump_18
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p0 p1 p3 p7 p4 p6 p5 p2 : Prop)
theorem file23_89163 : ((((((p3 → False) ∨ (p5 ∧ True)) ∨ ((p4 → p4) ∨ (p4 ∨ p0))) → (((p4 → True) ∧ (False ∧ p6)) → False)) ∧ ((((True → False) ∨ (p6 ∧ p1)) → ((False → p6) → False)) ∧ (((p2 ∨ True) → False) ∧ ((True ∧ p7) ∧ (False ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case inl assump_22 =>
              apply False.elim assump_22
            case inr assump_23 =>
              have assump_34 : (p2 ∨ True) := by
                apply Or.inl
                exact assump_23
              let assump_30 := assump_10 assump_34
              apply False.elim assump_30


variable (p0 p2 p7 p5 p6 p3 p1 : Prop)
theorem file23_90120 : ((((((p5 → p1) → False) ∨ ((False → False) ∨ (False ∨ p2))) → (((p2 ∧ p7) → (p5 ∧ p3)) → ((False ∧ p0) ∨ (False ∨ p1)))) ∧ ((((True ∨ False) → False) → ((p2 → p6) → (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((True ∨ False) → False) → ((p2 → p6) → (p0 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      have assump_26 : (True ∨ False) := by
        apply Or.inl
        apply True.intro
      let assump_18 := assump_9 assump_26
      apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p2 p4 p5 p7 p6 p1 p3 p0 : Prop)
theorem file23_90841 : (((((p5 → p4) → (False ∨ p5)) → ((False ∧ True) → False)) → False) → ((((p2 → False) ∧ (p6 ∧ p1)) → ((p5 ∨ p1) ∧ (True → False))) ∧ (((p7 → False) → (p3 → True)) ∨ ((p0 → False) → (p3 ∨ p0))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply Or.inr
      exact assump_8
  intro assump_15
  cases assump_2
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      have assump_44 : (((p5 → p4) → (False ∨ p5)) → ((False ∧ True) → False)) := by
        intro assump_31
        intro assump_32
        cases assump_32
        case intro assump_33 assump_34 =>
          apply False.elim assump_33
      let assump_30 := assump_1 assump_44
      apply False.elim assump_30
  apply Or.inl
  intro assump_42
  intro assump_43
  apply True.intro


variable (p4 p1 p6 p0 p5 p7 : Prop)
theorem file23_91827 : (((((p7 → False) → False) → ((p5 ∧ p0) → (p4 ∨ p4))) → False) → ((((p1 ∧ p7) ∨ (p4 → p4)) ∧ ((p7 ∧ p5) ∨ (True ∨ True))) ∨ (((p0 → p4) ∨ (p7 ∨ p6)) ∧ ((p7 → p0) → False)))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_4
  exact assump_4
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p4 p6 p1 p3 p5 p2 : Prop)
theorem file23_92214 : ((((((p6 → False) → (True → p6)) → ((p6 ∧ p3) → (False → False))) → False) ∧ ((((p5 ∨ p5) ∧ (False ∧ False)) → ((p6 → True) → (False ∧ p1))) ∨ (((p2 ∧ p4) ∧ (p3 → False)) ∨ ((p5 ∧ p5) ∧ (True ∨ p5))))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case inl assump_14 =>
      have assump_89 : (((p6 → False) → (True → p6)) → ((p6 ∧ p3) → (False → False))) := by
        intro assump_20
        intro assump_21
        intro assump_22
        apply False.elim assump_22
      let assump_19 := assump_10 assump_89
      apply False.elim assump_19
    case inr assump_15 =>
      cases assump_15
      case inl assump_28 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            have assump_90 : (((p6 → False) → (True → p6)) → ((p6 ∧ p3) → (False → False))) := by
              intro assump_44
              intro assump_45
              intro assump_46
              apply False.elim assump_46
            let assump_43 := assump_10 assump_90
            apply False.elim assump_43
      case inr assump_29 =>
        cases assump_29
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_53
            case inl assump_60 =>
              have assump_91 : (((p6 → False) → (True → p6)) → ((p6 ∧ p3) → (False → False))) := by
                intro assump_67
                intro assump_68
                intro assump_69
                apply False.elim assump_69
              let assump_66 := assump_10 assump_91
              apply False.elim assump_66
            case inr assump_61 =>
              have assump_92 : (((p6 → False) → (True → p6)) → ((p6 ∧ p3) → (False → False))) := by
                intro assump_81
                intro assump_82
                intro assump_83
                apply False.elim assump_83
              let assump_80 := assump_10 assump_92
              apply False.elim assump_80


variable (p6 p4 p0 p2 p7 p5 p1 : Prop)
theorem file23_94336 : (((((p4 ∧ p5) ∨ (p2 ∨ p2)) → ((p6 ∧ False) → (p6 ∧ p0))) → False) → ((((p1 ∨ p1) → False) ∨ ((p0 → False) ∧ (p7 ∧ p7))) → (((p1 → False) → False) → ((p6 ∨ p0) ∨ (p2 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_60 : (((p4 ∧ p5) ∨ (p2 ∨ p2)) → ((p6 ∧ False) → (p6 ∧ p0))) := by
      intro assump_13
      intro assump_14
      apply And.intro
      cases assump_14
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
      cases assump_14
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
    let assump_12 := assump_1 assump_60
    apply False.elim assump_12
  case inr assump_7 =>
    cases assump_7
    case intro assump_30 assump_31 =>
      cases assump_31
      case intro assump_34 assump_35 =>
        have assump_61 : (((p4 ∧ p5) ∨ (p2 ∨ p2)) → ((p6 ∧ False) → (p6 ∧ p0))) := by
          intro assump_43
          intro assump_44
          apply And.intro
          cases assump_44
          case intro assump_45 assump_46 =>
            apply False.elim assump_46
          cases assump_44
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
        let assump_42 := assump_1 assump_61
        apply False.elim assump_42


variable (p3 p2 p6 p5 p4 p7 p0 p1 : Prop)
theorem file23_95690 : ((((((p1 → p0) → False) → ((p5 → False) ∧ (True ∨ False))) ∨ (((p2 → False) ∨ (p6 ∧ p6)) → ((True ∧ p5) ∧ (p6 → False)))) ∧ ((((p4 ∧ False) → (p5 → True)) → False) ∧ (((p3 ∨ p6) ∧ (p0 ∧ p7)) ∨ ((False ∧ p3) → (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                have assump_116 : ((p4 ∧ False) → (p5 → True)) := by
                  intro assump_30
                  intro assump_31
                  apply True.intro
                let assump_29 := assump_8 assump_116
                apply False.elim assump_29
            case inr assump_17 =>
              cases assump_15
              case intro assump_37 assump_38 =>
                have assump_117 : ((p4 ∧ False) → (p5 → True)) := by
                  intro assump_47
                  intro assump_48
                  apply True.intro
                let assump_46 := assump_8 assump_117
                apply False.elim assump_46
        case inr assump_13 =>
          have assump_118 : ((p4 ∧ False) → (p5 → True)) := by
            intro assump_56
            intro assump_57
            apply True.intro
          let assump_55 := assump_8 assump_118
          apply False.elim assump_55
    case inr assump_5 =>
      cases assump_3
      case intro assump_63 assump_64 =>
        cases assump_64
        case inl assump_67 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            cases assump_69
            case inl assump_71 =>
              cases assump_70
              case intro assump_75 assump_76 =>
                have assump_119 : ((p4 ∧ False) → (p5 → True)) := by
                  intro assump_85
                  intro assump_86
                  apply True.intro
                let assump_84 := assump_63 assump_119
                apply False.elim assump_84
            case inr assump_72 =>
              cases assump_70
              case intro assump_92 assump_93 =>
                have assump_120 : ((p4 ∧ False) → (p5 → True)) := by
                  intro assump_102
                  intro assump_103
                  apply True.intro
                let assump_101 := assump_63 assump_120
                apply False.elim assump_101
        case inr assump_68 =>
          have assump_121 : ((p4 ∧ False) → (p5 → True)) := by
            intro assump_111
            intro assump_112
            apply True.intro
          let assump_110 := assump_63 assump_121
          apply False.elim assump_110


variable (p2 p4 p1 p0 p7 p6 p5 p3 : Prop)
theorem file23_98612 : ((((((False → p3) → (p5 ∧ p7)) ∨ ((False → p1) ∨ (p2 → p7))) → (((p0 ∨ p6) → False) → False)) ∧ ((((p3 ∨ p2) ∨ (p0 → False)) ∧ ((p4 ∨ p7) → (p3 → p4))) ∧ (((p4 ∧ False) ∨ (True ∧ True)) → False))) → False) := by
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
            have assump_44 : ((p4 ∧ False) ∨ (True ∧ True)) := by
              apply Or.inr
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_20 := assump_7 assump_44
            apply False.elim assump_20
          case inr assump_13 =>
            have assump_45 : ((p4 ∧ False) ∨ (True ∧ True)) := by
              apply Or.inr
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_30 := assump_7 assump_45
            apply False.elim assump_30
        case inr assump_11 =>
          have assump_46 : ((p4 ∧ False) ∨ (True ∧ True)) := by
            apply Or.inr
            apply And.intro
            apply True.intro
            apply True.intro
          let assump_40 := assump_7 assump_46
          apply False.elim assump_40


variable (p3 p7 p2 : Prop)
theorem file23_100032 : (((((p7 ∧ p7) ∧ (p7 → False)) → False) → False) → ((((True ∨ False) → (p7 → p2)) ∧ ((p3 → False) → (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_30 : (((p7 ∧ p7) ∧ (p7 → False)) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          have assump_31 : p7 := by
            exact assump_16
          let assump_23 := assump_14 assump_31
          apply False.elim assump_23
    let assump_11 := assump_1 assump_30
    apply False.elim assump_11


variable (p1 p4 p7 p5 p3 p0 p2 p6 : Prop)
theorem file23_100746 : (((((True ∧ p3) → False) → ((p6 ∨ True) → (False → False))) ∨ (((p6 → False) → (p7 ∨ p7)) ∨ ((p3 → False) → (p5 ∧ p0)))) ∨ ((((p2 ∨ p6) ∧ (p4 ∧ p0)) ∨ ((p0 → p2) ∨ (p4 ∧ p5))) → (((p5 → p4) ∧ (p1 → False)) ∧ ((False ∨ False) ∧ (p6 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p1 p7 p0 : Prop)
theorem file23_101156 : (((((p0 ∧ p0) ∨ (False → False)) → False) ∧ (((True → True) → False) ∨ ((p1 → False) ∧ (p1 ∧ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_31 : (True → True) := by
        intro assump_11
        apply True.intro
      let assump_10 := assump_6 assump_31
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          have assump_32 : p1 := by
            exact assump_19
          let assump_27 := assump_15 assump_32
          apply False.elim assump_27


variable (p1 p2 p6 : Prop)
theorem file23_101901 : (((((p2 → p6) → False) → ((True ∨ False) ∧ (p6 → False))) → (((p1 → False) → (True ∨ True)) → False)) → False) := by
  intro assump_1
  have assump_27 : (((p2 → p6) → False) → ((True ∨ False) ∧ (p6 → False))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_8
    have assump_28 : (p2 → p6) := by
      intro assump_14
      exact assump_8
    let assump_13 := assump_5 assump_28
    apply False.elim assump_13
  let assump_4 := assump_1 assump_27
  have assump_29 : ((p1 → False) → (True ∨ True)) := by
    intro assump_21
    apply Or.inl
    apply True.intro
  let assump_20 := assump_4 assump_29
  apply False.elim assump_20


variable (p0 : Prop)
theorem file23_102626 : ((((((True → False) → (False ∧ p0)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True → False) → (False ∧ p0)) → False) → False) := by
    intro assump_5
    have assump_29 : ((True → False) → (False ∧ p0)) := by
      intro assump_9
      apply And.intro
      have assump_30 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_30
      apply False.elim assump_12
      have assump_31 : True := by
        apply True.intro
      let assump_18 := assump_9 assump_31
      apply False.elim assump_18
    let assump_8 := assump_5 assump_29
    apply False.elim assump_8
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p3 p5 p4 p7 p0 p2 p1 p6 : Prop)
theorem file23_103387 : ((((((True → p7) → False) ∨ ((p6 ∧ p7) → (p1 ∨ True))) ∧ (((True ∧ p7) ∧ (False ∧ p4)) ∧ ((p7 ∨ p0) → False))) ∧ ((((p3 → p6) → False) ∨ ((p3 ∨ True) → (False ∨ True))) → (((p2 → False) ∨ (p5 ∧ p0)) → ((p0 ∨ p6) → (p2 → False))))) → False) := by
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
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
      case inr assump_7 =>
        cases assump_5
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              cases assump_29
              case intro assump_36 assump_37 =>
                apply False.elim assump_36


variable (p4 p1 p7 p3 p0 p6 : Prop)
theorem file23_104551 : (((((p3 → False) → (p0 ∧ p3)) → ((p3 → p0) ∧ (p4 ∧ True))) ∧ (((True → True) → False) ∧ ((p7 ∨ p0) ∨ (p7 → p1)))) → ((((p7 → False) → (p6 → False)) ∨ ((p4 → False) → (p0 ∨ p1))) ∨ (((p6 ∧ p6) → False) ∨ ((p0 → False) → (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          intro assump_16
          intro assump_17
          have assump_58 : p7 := by
            exact assump_12
          let assump_22 := assump_16 assump_58
          apply False.elim assump_22
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_28
          intro assump_29
          have assump_59 : (True → True) := by
            intro assump_38
            apply True.intro
          let assump_37 := assump_6 assump_59
          apply False.elim assump_37
      case inr assump_11 =>
        apply Or.inl
        apply Or.inl
        intro assump_44
        intro assump_45
        have assump_60 : (True → True) := by
          intro assump_54
          apply True.intro
        let assump_53 := assump_6 assump_60
        apply False.elim assump_53


variable (p5 p4 p0 p2 p6 p1 : Prop)
theorem file23_105935 : ((((((p1 ∧ p2) → (False ∨ p6)) → False) → (((p0 ∧ p6) → (False → p4)) ∧ ((p5 ∧ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p1 ∧ p2) → (False ∨ p6)) → False) → (((p0 ∧ p6) → (False → p4)) ∧ ((p5 ∧ p6) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    apply False.elim assump_7
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      have assump_34 : ((p1 ∧ p2) → (False ∨ p6)) := by
        intro assump_20
        cases assump_20
        case intro assump_21 assump_22 =>
          apply Or.inr
          exact assump_12
      let assump_19 := assump_5 assump_34
      apply False.elim assump_19
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p7 p1 p4 p0 p6 p2 : Prop)
theorem file23_106767 : (((((p0 → p0) → (False → False)) → False) → False) → ((((p4 → p6) ∨ (p2 → False)) ∨ ((p7 → False) → (p2 → True))) → (((p2 ∧ p2) → (False → False)) ∨ ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      intro assump_11
      intro assump_12
      apply False.elim assump_12
    case inr assump_6 =>
      apply Or.inl
      intro assump_19
      intro assump_20
      apply False.elim assump_20
  case inr assump_4 =>
    apply Or.inl
    intro assump_27
    intro assump_28
    apply False.elim assump_28


variable (p4 p2 p6 p5 p0 p7 p1 : Prop)
theorem file23_107457 : (((((p4 → p5) → False) ∨ ((p6 → False) ∨ (p6 ∨ p0))) → False) → ((((p1 ∨ p4) → False) ∧ ((p7 ∨ p2) ∨ (p1 ∨ p4))) → (((True → False) → (True ∧ p6)) ∨ ((False → p0) → (False ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_15
        apply And.intro
        apply True.intro
        have assump_57 : True := by
          apply True.intro
        let assump_18 := assump_15 assump_57
        apply False.elim assump_18
      case inr assump_10 =>
        apply Or.inl
        intro assump_26
        apply And.intro
        apply True.intro
        have assump_58 : True := by
          apply True.intro
        let assump_29 := assump_26 assump_58
        apply False.elim assump_29
    case inr assump_8 =>
      cases assump_8
      case inl assump_33 =>
        apply Or.inl
        intro assump_39
        apply And.intro
        apply True.intro
        have assump_59 : True := by
          apply True.intro
        let assump_42 := assump_39 assump_59
        apply False.elim assump_42
      case inr assump_34 =>
        apply Or.inl
        intro assump_50
        apply And.intro
        apply True.intro
        have assump_60 : True := by
          apply True.intro
        let assump_53 := assump_50 assump_60
        apply False.elim assump_53


variable (p2 p4 p1 p6 p5 : Prop)
theorem file23_108959 : (((((True → False) → False) → ((p6 ∨ True) → False)) → (((p1 ∨ p5) → False) → False)) ∨ ((((p2 → False) → (False → p4)) → ((p1 ∧ True) → (False → True))) → (((p1 ∧ p6) → (p1 ∧ p4)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_19 : ((True → False) → False) := by
    intro assump_8
    have assump_20 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_20
    apply False.elim assump_11
  let assump_7 := assump_1 assump_19
  have assump_21 : (p6 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_15 := assump_7 assump_21
  apply False.elim assump_15


variable (p0 p3 p1 : Prop)
theorem file23_109631 : (((((p1 ∨ p3) → False) → ((False → p0) ∨ (True → False))) → False) → False) := by
  intro assump_17
  have assump_30 : (((p1 ∨ p3) → False) → ((False → p0) ∨ (True → False))) := by
    intro assump_21
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
  let assump_20 := assump_17 assump_30
  apply False.elim assump_20


variable (p3 p1 p6 p7 : Prop)
theorem file23_110022 : ((((((p7 → False) → (p3 → p3)) → False) → (((p6 ∧ p7) ∧ (p1 → p6)) ∧ ((p6 ∨ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_79 : ((((p7 → False) → (p3 → p3)) → False) → (((p6 ∧ p7) ∧ (p1 → p6)) ∧ ((p6 ∨ p3) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    apply And.intro
    have assump_80 : ((p7 → False) → (p3 → p3)) := by
      intro assump_9
      intro assump_10
      exact assump_10
    let assump_8 := assump_5 assump_80
    apply False.elim assump_8
    have assump_81 : ((p7 → False) → (p3 → p3)) := by
      intro assump_21
      intro assump_22
      exact assump_22
    let assump_20 := assump_5 assump_81
    apply False.elim assump_20
    intro assump_30
    have assump_82 : ((p7 → False) → (p3 → p3)) := by
      intro assump_36
      intro assump_37
      exact assump_37
    let assump_35 := assump_5 assump_82
    apply False.elim assump_35
    intro assump_45
    cases assump_45
    case inl assump_46 =>
      have assump_83 : ((p7 → False) → (p3 → p3)) := by
        intro assump_53
        intro assump_54
        exact assump_54
      let assump_52 := assump_5 assump_83
      apply False.elim assump_52
    case inr assump_47 =>
      have assump_84 : ((p7 → False) → (p3 → p3)) := by
        intro assump_67
        intro assump_68
        exact assump_68
      let assump_66 := assump_5 assump_84
      apply False.elim assump_66
  let assump_4 := assump_1 assump_79
  apply False.elim assump_4


variable (p0 p3 p1 p7 p4 : Prop)
theorem file23_111557 : ((((((p4 → False) ∧ (True → False)) → ((p4 → p3) ∨ (True → p1))) ∨ (((p7 → p0) → False) → False)) → False) → False) := by
  intro assump_9
  have assump_31 : ((((p4 → False) ∧ (True → False)) → ((p4 → p3) ∨ (True → p1))) ∨ (((p7 → p0) → False) → False)) := by
    apply Or.inl
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply Or.inl
      intro assump_20
      have assump_32 : True := by
        apply True.intro
      let assump_24 := assump_15 assump_32
      apply False.elim assump_24
  let assump_12 := assump_9 assump_31
  apply False.elim assump_12


variable (p3 p1 p0 p5 p4 p2 : Prop)
theorem file23_112215 : ((((((p1 ∨ p3) ∧ (p5 ∧ p2)) ∨ ((p4 → False) ∧ (p5 ∨ p3))) ∧ (((p1 → True) ∧ (p4 ∨ p0)) → False)) ∧ ((((p0 ∧ False) → False) → ((True → False) → False)) → (((p0 ∨ True) → (False → False)) → False))) → False) := by
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
            cases assump_9
            case intro assump_14 assump_15 =>
              have assump_134 : (((p0 ∧ False) → False) → ((True → False) → False)) := by
                intro assump_25
                intro assump_26
                have assump_135 : True := by
                  apply True.intro
                let assump_32 := assump_26 assump_135
                apply False.elim assump_32
              let assump_24 := assump_3 assump_134
              have assump_136 : ((p0 ∨ True) → (False → False)) := by
                intro assump_37
                intro assump_38
                apply False.elim assump_38
              let assump_36 := assump_24 assump_136
              apply False.elim assump_36
          case inr assump_11 =>
            cases assump_9
            case intro assump_46 assump_47 =>
              have assump_137 : (((p0 ∧ False) → False) → ((True → False) → False)) := by
                intro assump_57
                intro assump_58
                have assump_138 : True := by
                  apply True.intro
                let assump_64 := assump_58 assump_138
                apply False.elim assump_64
              let assump_56 := assump_3 assump_137
              have assump_139 : ((p0 ∨ True) → (False → False)) := by
                intro assump_69
                intro assump_70
                apply False.elim assump_70
              let assump_68 := assump_56 assump_139
              apply False.elim assump_68
      case inr assump_7 =>
        cases assump_7
        case intro assump_76 assump_77 =>
          cases assump_77
          case inl assump_80 =>
            have assump_140 : (((p0 ∧ False) → False) → ((True → False) → False)) := by
              intro assump_89
              intro assump_90
              have assump_141 : True := by
                apply True.intro
              let assump_96 := assump_90 assump_141
              apply False.elim assump_96
            let assump_88 := assump_3 assump_140
            have assump_142 : ((p0 ∨ True) → (False → False)) := by
              intro assump_101
              intro assump_102
              apply False.elim assump_102
            let assump_100 := assump_88 assump_142
            apply False.elim assump_100
          case inr assump_81 =>
            have assump_143 : (((p0 ∧ False) → False) → ((True → False) → False)) := by
              intro assump_115
              intro assump_116
              have assump_144 : True := by
                apply True.intro
              let assump_122 := assump_116 assump_144
              apply False.elim assump_122
            let assump_114 := assump_3 assump_143
            have assump_145 : ((p0 ∨ True) → (False → False)) := by
              intro assump_127
              intro assump_128
              apply False.elim assump_128
            let assump_126 := assump_114 assump_145
            apply False.elim assump_126


variable (p2 p0 p7 p6 p5 : Prop)
theorem file23_115705 : ((((((p6 ∧ p0) → False) ∧ ((p0 → True) ∧ (p6 ∧ p7))) → (((p2 ∨ p5) → False) → ((p6 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p6 ∧ p0) → False) ∧ ((p0 → True) ∧ (p6 ∧ p7))) → (((p2 ∨ p5) → False) → ((p6 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          have assump_39 : p6 := by
            exact assump_20
          let assump_31 := assump_7 assump_39
          apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p4 p1 p2 p6 p0 p5 p7 p3 : Prop)
theorem file23_116495 : ((((((p4 ∨ p6) ∨ (True ∨ True)) → False) ∨ (((p4 → p3) ∨ (p7 ∨ p5)) ∧ ((p0 → p0) → False))) ∧ ((((p1 ∧ p6) ∨ (p1 ∧ False)) → ((False ∧ True) → False)) ∧ (((p1 ∧ p4) → False) ∧ ((p4 → True) ∧ (True → p2))))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_20
      case intro assump_25 assump_26 =>
        cases assump_26
        case intro assump_29 assump_30 =>
          cases assump_30
          case intro assump_33 assump_34 =>
            have assump_144 : ((p4 ∨ p6) ∨ (True ∨ True)) := by
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_44 := assump_21 assump_144
            apply False.elim assump_44
    case inr assump_22 =>
      cases assump_22
      case intro assump_48 assump_49 =>
        cases assump_48
        case inl assump_50 =>
          cases assump_20
          case intro assump_56 assump_57 =>
            cases assump_57
            case intro assump_60 assump_61 =>
              cases assump_61
              case intro assump_64 assump_65 =>
                have assump_145 : (p0 → p0) := by
                  intro assump_76
                  exact assump_76
                let assump_75 := assump_49 assump_145
                apply False.elim assump_75
        case inr assump_51 =>
          cases assump_51
          case inl assump_82 =>
            cases assump_20
            case intro assump_88 assump_89 =>
              cases assump_89
              case intro assump_92 assump_93 =>
                cases assump_93
                case intro assump_96 assump_97 =>
                  have assump_146 : (p0 → p0) := by
                    intro assump_108
                    exact assump_108
                  let assump_107 := assump_49 assump_146
                  apply False.elim assump_107
          case inr assump_83 =>
            cases assump_20
            case intro assump_118 assump_119 =>
              cases assump_119
              case intro assump_122 assump_123 =>
                cases assump_123
                case intro assump_126 assump_127 =>
                  have assump_147 : (p0 → p0) := by
                    intro assump_138
                    exact assump_138
                  let assump_137 := assump_49 assump_147
                  apply False.elim assump_137


variable (p3 p2 p7 p4 p0 : Prop)
theorem file23_118961 : (((((True ∨ p4) ∨ (p0 ∧ False)) ∨ ((p2 ∧ p7) ∧ (p7 → p4))) ∧ (((p3 → False) → (p4 ∨ p4)) → False)) → ((((p4 ∨ p2) → False) → ((True ∨ p3) ∨ (p0 → p4))) ∨ (((p2 ∨ True) → (True ∨ p3)) → False))) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_31
    case inl assump_33 =>
      cases assump_33
      case inl assump_35 =>
        cases assump_35
        case inl assump_37 =>
          apply Or.inl
          intro assump_43
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_38 =>
          apply Or.inl
          intro assump_50
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_36 =>
        cases assump_36
        case intro assump_53 assump_54 =>
          apply False.elim assump_54
    case inr assump_34 =>
      cases assump_34
      case intro assump_59 assump_60 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          apply Or.inl
          intro assump_71
          apply Or.inl
          apply Or.inl
          apply True.intro


variable (p1 p6 p0 p7 p4 p3 p2 p5 : Prop)
theorem file23_120130 : (((((p7 → False) ∨ (p6 ∧ p0)) → ((p3 → True) ∧ (True → p7))) ∨ (((p1 → p3) → (p4 → False)) → ((p1 → p5) → False))) → ((((p4 → p6) ∨ (p1 → p5)) ∧ ((p7 ∧ True) → False)) → (((False ∧ p4) ∨ (True ∨ p2)) ∨ ((p3 ∧ p4) ∧ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case inl assump_11 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
    case inr assump_6 =>
      cases assump_1
      case inl assump_21 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      case inr assump_22 =>
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro


variable (p5 p0 p4 p1 p2 p6 p3 : Prop)
theorem file23_121091 : ((((((False → p6) → (p3 ∧ p4)) → ((p6 ∨ p4) → False)) ∧ (((p3 ∨ p6) ∧ (False ∧ p1)) ∧ ((p0 → False) → (p1 → False)))) ∧ ((((p0 ∨ p6) ∨ (p5 ∧ p6)) → False) ∨ (((p5 → False) → (False → False)) ∨ ((p2 ∨ p6) → False)))) → False) := by
  intro assump_64
  cases assump_64
  case intro assump_65 assump_66 =>
    cases assump_65
    case intro assump_67 assump_68 =>
      cases assump_68
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_73
          case inl assump_75 =>
            cases assump_74
            case intro assump_79 assump_80 =>
              apply False.elim assump_79
          case inr assump_76 =>
            cases assump_74
            case intro assump_85 assump_86 =>
              apply False.elim assump_85


variable (p4 p1 p6 p7 p0 p5 : Prop)
theorem file23_121960 : (((((p6 ∨ p1) → False) → ((p5 ∧ p4) ∧ (p0 → p1))) ∧ (((p4 → p0) → (False → p6)) → False)) → ((((p7 ∨ False) → (p6 → True)) ∨ ((p4 → False) ∧ (p0 → p4))) → (((p4 → False) → False) → ((p5 ∧ p6) ∨ (p4 → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      apply Or.inr
      intro assump_16
      exact assump_16
  case inr assump_7 =>
    cases assump_7
    case intro assump_19 assump_20 =>
      cases assump_1
      case intro assump_25 assump_26 =>
        apply Or.inr
        intro assump_31
        exact assump_31


variable (p0 p3 p4 p6 : Prop)
theorem file23_122649 : ((((((False ∧ p0) → False) → False) → (((p4 → p6) → (p3 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False ∧ p0) → False) → False) → (((p4 → p6) → (p3 → p3)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_24 : ((False ∧ p0) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_11 := assump_5 assump_24
    apply False.elim assump_11
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p6 p3 p2 p5 p7 p4 : Prop)
theorem file23_123262 : ((((((p2 ∧ p6) ∧ (p7 → False)) ∧ ((p4 ∨ p2) ∨ (p3 ∧ p5))) → (((p3 → p6) ∨ (p5 → False)) ∨ ((p5 → False) ∨ (p3 → False)))) ∧ ((((p2 → False) ∧ (p6 → False)) → False) ∧ (((p7 ∨ p7) → (True ∧ p4)) ∧ ((False → p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_23 : (False → p3) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_11 assump_23
        apply False.elim assump_16


