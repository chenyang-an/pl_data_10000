variable (p4 p0 p5 p6 p1 : Prop)
theorem file95_41 : (((((p5 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p4 → False))) → False) → ((((False → False) ∨ (True → p0)) → False) ∨ (((p4 ∧ p0) ∨ (p1 → p6)) ∨ ((False ∧ p1) ∨ (p0 ∨ p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_22 : (((p5 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p4 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_10 := assump_1 assump_22
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_23 : (((p5 ∨ True) ∨ (p5 ∨ p0)) ∨ ((p4 → False) ∨ (p4 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_18 := assump_1 assump_23
    apply False.elim assump_18


variable (p4 p6 p7 p2 p3 : Prop)
theorem file95_867 : (((((p6 → p2) → False) → ((p7 ∧ p2) → (p3 → p4))) → False) → False) := by
  intro assump_1
  have assump_28 : (((p6 → p2) → False) → ((p7 ∧ p2) → (p3 → p4))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_29 : (p6 → p2) := by
        intro assump_19
        exact assump_11
      let assump_18 := assump_5 assump_29
      apply False.elim assump_18
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p3 p6 p5 p1 : Prop)
theorem file95_1426 : (((((p3 ∧ p1) ∧ (p5 → p6)) → ((p3 → False) → (True → p3))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p3 ∧ p1) ∧ (p5 → p6)) → ((p3 → False) → (True → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        exact assump_14
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p4 p5 p3 p2 p7 : Prop)
theorem file95_1933 : (((((p7 → p5) → False) ∧ ((p7 ∨ p1) ∨ (False → False))) → False) → ((((p4 ∧ False) → (True → False)) → False) → (((p2 → p2) ∧ (p2 → True)) ∨ ((p3 ∧ p1) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply And.intro
  intro assump_7
  exact assump_7
  intro assump_10
  apply True.intro


variable (p1 p6 p3 p7 p5 p4 p0 p2 : Prop)
theorem file95_2314 : (((((True ∧ p6) → False) → ((p4 → True) ∧ (False ∨ p4))) ∨ (((p1 ∨ p0) → (p1 ∧ False)) → False)) → ((((p2 ∧ p4) ∨ (p3 → p5)) → ((p5 ∧ p6) → (p1 → p5))) ∨ (((p5 → False) ∨ (p5 ∨ p2)) ∧ ((p3 → p0) ∨ (p4 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_6
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          exact assump_11
      case inr assump_18 =>
        exact assump_11
  case inr assump_3 =>
    apply Or.inl
    intro assump_29
    intro assump_30
    intro assump_31
    cases assump_30
    case intro assump_34 assump_35 =>
      cases assump_29
      case inl assump_40 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          exact assump_34
      case inr assump_41 =>
        exact assump_34


variable (p4 p0 p7 p3 p2 p6 p1 : Prop)
theorem file95_3327 : (((((p1 → False) → False) ∨ ((p2 → False) ∨ (p3 → p6))) → (((p0 → True) ∧ (False → p0)) ∨ ((p7 → p3) → False))) ∨ ((((p6 → False) ∧ (p1 ∧ p4)) → False) ∧ (((p1 ∧ p4) ∧ (True → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    intro assump_6
    apply True.intro
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      apply Or.inl
      apply And.intro
      intro assump_14
      apply True.intro
      intro assump_15
      apply False.elim assump_15
    case inr assump_11 =>
      apply Or.inl
      apply And.intro
      intro assump_20
      apply True.intro
      intro assump_21
      apply False.elim assump_21


variable (p5 p0 p4 p6 : Prop)
theorem file95_4156 : (((((p4 → False) → (p6 ∨ False)) → ((p5 → p0) ∨ (p0 → False))) ∧ (((False → False) ∨ (p5 ∧ False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p5 ∧ False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p4 p2 p7 p5 p6 : Prop)
theorem file95_4609 : ((((((True ∨ False) → False) ∧ ((p2 ∧ p7) ∨ (True ∧ p5))) → (((p6 → p4) → (p7 ∨ False)) ∨ ((p2 ∧ p0) → (True → p6)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((True ∨ False) → False) ∧ ((p2 ∧ p7) ∨ (True ∧ p5))) → (((p6 → p4) → (p7 ∨ False)) ∨ ((p2 ∧ p0) → (True → p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          apply Or.inl
          exact assump_13
      case inr assump_11 =>
        cases assump_11
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          have assump_40 : (True ∨ False) := by
            apply Or.inl
            apply True.intro
          let assump_32 := assump_6 assump_40
          apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p0 p1 p6 p5 : Prop)
theorem file95_5643 : ((((((p5 → False) ∧ (p0 ∧ False)) → ((p1 → False) → False)) ∨ (((True → p1) ∨ (p0 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 → False) ∧ (p0 ∧ False)) → ((p1 → False) → False)) ∨ (((True → p1) ∨ (p0 → p6)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p1 p5 p6 p7 p0 : Prop)
theorem file95_6238 : ((((((p5 → p5) → (p1 → False)) ∧ ((True → False) ∧ (False → p0))) → (((p5 ∨ p5) → (p5 ∧ p7)) → ((p5 ∧ p2) ∨ (p6 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p5 → p5) → (p1 → False)) ∧ ((True → False) ∧ (False → p0))) → (((p5 ∨ p5) → (p5 ∧ p7)) → ((p5 ∧ p2) ∨ (p6 ∧ p7)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_28 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_28
        apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p1 p0 p7 p5 p6 p4 p3 : Prop)
theorem file95_6971 : ((((((True ∨ p7) → (p5 → False)) → ((p5 ∧ p4) → (p6 → False))) ∨ (((p4 → p1) → False) → ((p5 ∧ p5) ∧ (p0 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True ∨ p7) → (p5 → False)) → ((p5 ∧ p4) → (p6 → False))) ∨ (((p4 → p1) → False) → ((p5 ∧ p5) ∧ (p0 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_27 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_18 := assump_5 assump_27
      have assump_28 : p5 := by
        exact assump_10
      let assump_19 := assump_18 assump_28
      apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p3 p5 : Prop)
theorem file95_7771 : (((((True → p5) → False) → False) ∧ (((p7 ∧ p5) → (p3 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p7 ∧ p5) → (p3 ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p0 p2 p1 p6 p7 p3 : Prop)
theorem file95_8237 : (((((p2 ∧ p7) → (p1 ∧ p3)) → False) ∧ (((p6 → False) ∧ (p0 → False)) ∧ ((p6 → p6) → (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : (p6 → p6) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_7 assump_24
        have assump_25 : True := by
          apply True.intro
        let assump_20 := assump_16 assump_25
        apply False.elim assump_20


variable (p5 p0 p7 p6 p2 p4 p1 p3 : Prop)
theorem file95_8882 : ((((((p5 → True) → (p3 ∨ p3)) → ((p4 → False) ∨ (p4 ∧ p1))) ∨ (((p6 → p1) → False) ∨ ((p5 ∧ p4) ∨ (p3 → False)))) ∧ ((((p5 → p2) ∨ (p2 → p0)) → False) ∧ (((p0 ∨ p1) ∨ (True → p2)) ∧ ((p7 ∧ False) ∧ (True ∨ False))))) → False) := by
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
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  apply False.elim assump_23
            case inr assump_17 =>
              cases assump_13
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_33
          case inr assump_15 =>
            cases assump_13
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                apply False.elim assump_43
    case inr assump_5 =>
      cases assump_5
      case inl assump_48 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            cases assump_56
            case inl assump_58 =>
              cases assump_58
              case inl assump_60 =>
                cases assump_57
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_67
              case inr assump_61 =>
                cases assump_57
                case intro assump_74 assump_75 =>
                  cases assump_74
                  case intro assump_76 assump_77 =>
                    apply False.elim assump_77
            case inr assump_59 =>
              cases assump_57
              case intro assump_84 assump_85 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  apply False.elim assump_87
      case inr assump_49 =>
        cases assump_49
        case inl assump_92 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            cases assump_3
            case intro assump_100 assump_101 =>
              cases assump_101
              case intro assump_104 assump_105 =>
                cases assump_104
                case inl assump_106 =>
                  cases assump_106
                  case inl assump_108 =>
                    cases assump_105
                    case intro assump_112 assump_113 =>
                      cases assump_112
                      case intro assump_114 assump_115 =>
                        apply False.elim assump_115
                  case inr assump_109 =>
                    cases assump_105
                    case intro assump_122 assump_123 =>
                      cases assump_122
                      case intro assump_124 assump_125 =>
                        apply False.elim assump_125
                case inr assump_107 =>
                  cases assump_105
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case intro assump_134 assump_135 =>
                      apply False.elim assump_135
        case inr assump_93 =>
          cases assump_3
          case intro assump_142 assump_143 =>
            cases assump_143
            case intro assump_146 assump_147 =>
              cases assump_146
              case inl assump_148 =>
                cases assump_148
                case inl assump_150 =>
                  cases assump_147
                  case intro assump_154 assump_155 =>
                    cases assump_154
                    case intro assump_156 assump_157 =>
                      apply False.elim assump_157
                case inr assump_151 =>
                  cases assump_147
                  case intro assump_164 assump_165 =>
                    cases assump_164
                    case intro assump_166 assump_167 =>
                      apply False.elim assump_167
              case inr assump_149 =>
                cases assump_147
                case intro assump_174 assump_175 =>
                  cases assump_174
                  case intro assump_176 assump_177 =>
                    apply False.elim assump_177


variable (p4 p7 p0 p6 p5 p1 : Prop)
theorem file95_13575 : (((((p6 ∨ True) ∧ (p5 ∨ True)) ∧ ((p1 ∨ p7) ∨ (p0 → p5))) ∧ (((p5 ∨ p6) ∨ (p6 ∧ p4)) → ((True ∨ p5) → False))) → ((((p4 ∧ p5) ∨ (False ∧ p1)) ∧ ((p1 → True) ∨ (p6 → p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_1
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                cases assump_21
                case inl assump_23 =>
                  cases assump_22
                  case inl assump_27 =>
                    cases assump_20
                    case inl assump_31 =>
                      cases assump_31
                      case inl assump_33 =>
                        have assump_319 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_27
                        let assump_39 := assump_18 assump_319
                        have assump_320 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_40 := assump_39 assump_320
                        apply False.elim assump_40
                      case inr assump_34 =>
                        have assump_321 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_27
                        let assump_48 := assump_18 assump_321
                        have assump_322 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_49 := assump_48 assump_322
                        apply False.elim assump_49
                    case inr assump_32 =>
                      have assump_323 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_27
                      let assump_57 := assump_18 assump_323
                      have assump_324 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_58 := assump_57 assump_324
                      apply False.elim assump_58
                  case inr assump_28 =>
                    cases assump_20
                    case inl assump_64 =>
                      cases assump_64
                      case inl assump_66 =>
                        have assump_325 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_72 := assump_18 assump_325
                        have assump_326 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_73 := assump_72 assump_326
                        apply False.elim assump_73
                      case inr assump_67 =>
                        have assump_327 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_81 := assump_18 assump_327
                        have assump_328 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_82 := assump_81 assump_328
                        apply False.elim assump_82
                    case inr assump_65 =>
                      have assump_329 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_8
                      let assump_90 := assump_18 assump_329
                      have assump_330 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_91 := assump_90 assump_330
                      apply False.elim assump_91
                case inr assump_24 =>
                  cases assump_22
                  case inl assump_97 =>
                    cases assump_20
                    case inl assump_101 =>
                      cases assump_101
                      case inl assump_103 =>
                        have assump_331 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_97
                        let assump_109 := assump_18 assump_331
                        have assump_332 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_110 := assump_109 assump_332
                        apply False.elim assump_110
                      case inr assump_104 =>
                        have assump_333 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_97
                        let assump_118 := assump_18 assump_333
                        have assump_334 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_119 := assump_118 assump_334
                        apply False.elim assump_119
                    case inr assump_102 =>
                      have assump_335 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_97
                      let assump_127 := assump_18 assump_335
                      have assump_336 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_128 := assump_127 assump_336
                      apply False.elim assump_128
                  case inr assump_98 =>
                    cases assump_20
                    case inl assump_134 =>
                      cases assump_134
                      case inl assump_136 =>
                        have assump_337 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_142 := assump_18 assump_337
                        have assump_338 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_143 := assump_142 assump_338
                        apply False.elim assump_143
                      case inr assump_137 =>
                        have assump_339 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_151 := assump_18 assump_339
                        have assump_340 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_152 := assump_151 assump_340
                        apply False.elim assump_152
                    case inr assump_135 =>
                      have assump_341 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_8
                      let assump_160 := assump_18 assump_341
                      have assump_342 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_161 := assump_160 assump_342
                      apply False.elim assump_161
        case inr assump_14 =>
          cases assump_1
          case intro assump_167 assump_168 =>
            cases assump_167
            case intro assump_169 assump_170 =>
              cases assump_169
              case intro assump_171 assump_172 =>
                cases assump_171
                case inl assump_173 =>
                  cases assump_172
                  case inl assump_177 =>
                    cases assump_170
                    case inl assump_181 =>
                      cases assump_181
                      case inl assump_183 =>
                        have assump_343 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_177
                        let assump_189 := assump_168 assump_343
                        have assump_344 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_190 := assump_189 assump_344
                        apply False.elim assump_190
                      case inr assump_184 =>
                        have assump_345 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_177
                        let assump_198 := assump_168 assump_345
                        have assump_346 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_199 := assump_198 assump_346
                        apply False.elim assump_199
                    case inr assump_182 =>
                      have assump_347 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_177
                      let assump_207 := assump_168 assump_347
                      have assump_348 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_208 := assump_207 assump_348
                      apply False.elim assump_208
                  case inr assump_178 =>
                    cases assump_170
                    case inl assump_214 =>
                      cases assump_214
                      case inl assump_216 =>
                        have assump_349 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_222 := assump_168 assump_349
                        have assump_350 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_223 := assump_222 assump_350
                        apply False.elim assump_223
                      case inr assump_217 =>
                        have assump_351 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_231 := assump_168 assump_351
                        have assump_352 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_232 := assump_231 assump_352
                        apply False.elim assump_232
                    case inr assump_215 =>
                      have assump_353 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_8
                      let assump_240 := assump_168 assump_353
                      have assump_354 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_241 := assump_240 assump_354
                      apply False.elim assump_241
                case inr assump_174 =>
                  cases assump_172
                  case inl assump_247 =>
                    cases assump_170
                    case inl assump_251 =>
                      cases assump_251
                      case inl assump_253 =>
                        have assump_355 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_247
                        let assump_259 := assump_168 assump_355
                        have assump_356 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_260 := assump_259 assump_356
                        apply False.elim assump_260
                      case inr assump_254 =>
                        have assump_357 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_247
                        let assump_268 := assump_168 assump_357
                        have assump_358 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_269 := assump_268 assump_358
                        apply False.elim assump_269
                    case inr assump_252 =>
                      have assump_359 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_247
                      let assump_277 := assump_168 assump_359
                      have assump_360 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_278 := assump_277 assump_360
                      apply False.elim assump_278
                  case inr assump_248 =>
                    cases assump_170
                    case inl assump_284 =>
                      cases assump_284
                      case inl assump_286 =>
                        have assump_361 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_292 := assump_168 assump_361
                        have assump_362 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_293 := assump_292 assump_362
                        apply False.elim assump_293
                      case inr assump_287 =>
                        have assump_363 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_8
                        let assump_301 := assump_168 assump_363
                        have assump_364 : (True ∨ p5) := by
                          apply Or.inl
                          apply True.intro
                        let assump_302 := assump_301 assump_364
                        apply False.elim assump_302
                    case inr assump_285 =>
                      have assump_365 : ((p5 ∨ p6) ∨ (p6 ∧ p4)) := by
                        apply Or.inl
                        apply Or.inl
                        exact assump_8
                      let assump_310 := assump_168 assump_365
                      have assump_366 : (True ∨ p5) := by
                        apply Or.inl
                        apply True.intro
                      let assump_311 := assump_310 assump_366
                      apply False.elim assump_311
    case inr assump_6 =>
      cases assump_6
      case intro assump_315 assump_316 =>
        apply False.elim assump_315


variable (p4 p2 p1 p6 p7 p0 : Prop)
theorem file95_29484 : ((((((p1 → True) ∨ (p6 ∨ p0)) → False) → (((False → p7) → (p6 → p7)) → ((p7 ∧ p2) ∨ (p7 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 → True) ∨ (p6 ∨ p0)) → False) → (((False → p7) → (p6 → p7)) → ((p7 ∧ p2) ∨ (p7 ∧ p4)))) := by
    intro assump_5
    intro assump_6
    have assump_20 : ((p1 → True) ∨ (p6 ∨ p0)) := by
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_11 := assump_5 assump_20
    apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p4 p6 p5 p7 : Prop)
theorem file95_30090 : (((((False → p4) → (p6 → False)) → False) ∧ (((p4 ∧ p4) → False) ∧ ((p7 ∨ True) → False))) → ((((p7 ∧ p5) ∨ (p1 → p4)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_19 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_15 := assump_10 assump_19
      apply False.elim assump_15


variable (p1 p5 p3 p0 p7 p2 p4 p6 : Prop)
theorem file95_30604 : ((((((p5 ∧ p6) ∧ (False ∨ p1)) → False) ∧ (((p2 → p6) ∨ (p3 ∧ False)) ∨ ((p4 → p0) → False))) ∧ ((((p0 → False) → False) ∨ ((p4 → False) → (p5 ∨ p7))) ∧ (((True ∨ False) ∧ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              have assump_74 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_23
                apply False.elim assump_23
              let assump_22 := assump_15 assump_74
              apply False.elim assump_22
            case inr assump_17 =>
              have assump_75 : ((True ∨ False) ∧ (False → False)) := by
                apply And.intro
                apply Or.inl
                apply True.intro
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_15 assump_75
              apply False.elim assump_33
        case inr assump_11 =>
          cases assump_11
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
      case inr assump_9 =>
        cases assump_3
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            have assump_76 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_57
              apply False.elim assump_57
            let assump_56 := assump_49 assump_76
            apply False.elim assump_56
          case inr assump_51 =>
            have assump_77 : ((True ∨ False) ∧ (False → False)) := by
              apply And.intro
              apply Or.inl
              apply True.intro
              intro assump_68
              apply False.elim assump_68
            let assump_67 := assump_49 assump_77
            apply False.elim assump_67


variable (p2 p5 p4 p1 p7 p0 : Prop)
theorem file95_32889 : (((((p5 ∨ p0) ∨ (p7 ∨ p7)) → False) → (((p1 ∨ p2) ∧ (p7 → p5)) → ((False ∧ False) → (True → p5)))) ∨ ((((p1 ∨ p2) ∨ (True ∨ p5)) ∨ ((p2 → False) → (p4 → False))) ∨ (((p2 ∧ True) ∧ (p5 → False)) → ((p2 → False) ∨ (p0 ∨ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    apply False.elim assump_7


variable (p3 p0 p5 p1 p4 : Prop)
theorem file95_33342 : (((((False → p4) → (p5 → p4)) → ((p0 ∨ True) ∨ (p3 → p1))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → p4) → (p5 → p4)) → ((p0 ∨ True) ∨ (p3 → p1))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p7 p1 : Prop)
theorem file95_33714 : (((((p1 → False) → (p7 ∨ p7)) → ((False → False) → (True ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 → False) → (p7 ∨ p7)) → ((False → False) → (True ∨ p4))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p1 p5 : Prop)
theorem file95_34100 : ((((((p5 → False) → False) → False) ∧ (((p6 ∨ p1) → False) → False)) ∧ ((((False ∨ False) → False) ∨ ((False → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((False ∨ False) → False) ∨ ((False → False) → False)) := by
        apply Or.inl
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply False.elim assump_15
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p1 p2 p6 p5 p7 p3 p0 : Prop)
theorem file95_34802 : (((((p7 ∧ False) → False) ∧ ((p0 ∨ p7) → (p2 ∨ p3))) ∧ (((p7 → False) ∨ (p1 → False)) ∨ ((p6 → False) ∧ (False → p1)))) → ((((p6 → True) ∨ (p5 → False)) ∨ ((p7 → False) → False)) ∨ (((False ∨ p2) ∨ (p0 ∧ p1)) ∧ ((p5 → p1) ∧ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_16
          apply True.intro
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_19
          apply True.intro
      case inr assump_11 =>
        cases assump_11
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_26
          apply True.intro


variable (p0 p5 p3 p1 : Prop)
theorem file95_35819 : ((((((True ∧ p3) ∧ (p5 ∧ False)) ∧ ((p5 → p1) ∨ (p0 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∧ p3) ∧ (p5 ∧ False)) ∧ ((p5 → p1) ∨ (p0 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p0 p4 p1 p5 p7 : Prop)
theorem file95_36458 : ((((((False ∧ p7) → False) → False) → (((p1 ∨ p0) → (p4 ∨ p2)) ∨ ((p5 → False) → (p7 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((False ∧ p7) → False) → False) → (((p1 ∨ p0) → (p4 ∨ p2)) ∨ ((p5 → False) → (p7 ∧ True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      have assump_39 : ((False ∧ p7) → False) := by
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_14 := assump_5 assump_39
      apply False.elim assump_14
    case inr assump_10 =>
      have assump_40 : ((False ∧ p7) → False) := by
        intro assump_27
        cases assump_27
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
      let assump_26 := assump_5 assump_40
      apply False.elim assump_26
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p6 p5 p1 : Prop)
theorem file95_37463 : (((((p6 → False) → False) → ((False ∧ p6) → False)) → False) → ((((p5 ∨ p5) ∧ (p1 ∧ False)) ∨ ((False ∨ p5) → False)) → False)) := by
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
          apply False.elim assump_12
      case inr assump_8 =>
        cases assump_6
        case intro assump_19 assump_20 =>
          apply False.elim assump_20
  case inr assump_4 =>
    have assump_39 : (((p6 → False) → False) → ((False ∧ p6) → False)) := by
      intro assump_30
      intro assump_31
      cases assump_31
      case intro assump_32 assump_33 =>
        apply False.elim assump_32
    let assump_29 := assump_1 assump_39
    apply False.elim assump_29


variable (p1 p4 p2 p0 p7 p3 : Prop)
theorem file95_38377 : ((((((p3 → False) → False) → False) ∧ (((p4 ∨ p0) → False) ∧ ((p0 ∨ False) ∨ (p2 → False)))) ∧ ((((p1 ∨ p2) → False) ∧ ((p0 ∧ p3) ∧ (False → p1))) ∨ (((p7 → p7) ∨ (p4 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_3
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    have assump_90 : (p4 ∨ p0) := by
                      apply Or.inr
                      exact assump_26
                    let assump_39 := assump_8 assump_90
                    apply False.elim assump_39
            case inr assump_19 =>
              have assump_91 : ((p7 → p7) ∨ (p4 → False)) := by
                apply Or.inl
                intro assump_46
                exact assump_46
              let assump_45 := assump_19 assump_91
              apply False.elim assump_45
          case inr assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          cases assump_3
          case inl assump_56 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                cases assump_62
                case intro assump_64 assump_65 =>
                  have assump_92 : (p4 ∨ p0) := by
                    apply Or.inr
                    exact assump_64
                  let assump_77 := assump_8 assump_92
                  apply False.elim assump_77
          case inr assump_57 =>
            have assump_93 : ((p7 → p7) ∨ (p4 → False)) := by
              apply Or.inl
              intro assump_84
              exact assump_84
            let assump_83 := assump_57 assump_93
            apply False.elim assump_83


variable (p4 p0 p1 p7 p2 p3 p5 : Prop)
theorem file95_40635 : (((((p7 ∨ p2) ∨ (p0 ∨ p5)) ∨ ((True → False) → (p3 → p4))) → False) → ((((p4 ∧ True) ∧ (p0 → False)) → False) ∨ (((p4 → p4) → False) → ((p1 → p0) ∨ (p7 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_27 : (((p7 ∨ p2) ∨ (p0 ∨ p5)) ∨ ((True → False) → (p3 → p4))) := by
        apply Or.inr
        intro assump_18
        intro assump_19
        exact assump_7
      let assump_17 := assump_1 assump_27
      apply False.elim assump_17


variable (p1 p2 p3 p0 p7 p4 p5 : Prop)
theorem file95_41274 : (((((True ∨ True) ∨ (p5 ∧ p1)) → False) ∧ (((p0 → False) ∧ (False ∨ p0)) ∨ ((False ∨ p4) → False))) → ((((p1 → False) → False) → ((True ∨ p7) ∨ (p3 ∧ p2))) ∨ (((p3 ∧ p2) → (p2 ∧ p7)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply Or.inl
          intro assump_18
          apply Or.inl
          apply Or.inl
          apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_23
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p3 p7 p6 p2 p1 p5 p4 : Prop)
theorem file95_42077 : (((((p7 ∧ p3) ∧ (p6 ∨ False)) → ((p1 → p5) ∨ (p2 ∨ p7))) ∨ (((p3 ∧ p3) → False) → ((p1 ∨ p4) ∧ (p2 ∧ True)))) → ((((p4 → p5) → False) ∧ ((p1 ∨ False) → (p3 → False))) → (((p5 → False) → (p5 → p2)) ∨ ((p3 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      intro assump_14
      have assump_35 : p5 := by
        exact assump_14
      let assump_19 := assump_13 assump_35
      apply False.elim assump_19
    case inr assump_10 =>
      apply Or.inl
      intro assump_25
      intro assump_26
      have assump_36 : p5 := by
        exact assump_26
      let assump_31 := assump_25 assump_36
      apply False.elim assump_31


variable (p3 p4 p1 p7 : Prop)
theorem file95_42907 : ((((((p1 ∨ p4) → False) ∨ ((p1 → True) → (p3 → False))) → (((p7 → p4) ∧ (p1 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p1 ∨ p4) → False) ∨ ((p1 → True) → (p3 → False))) → (((p7 → p4) ∧ (p1 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p4 : Prop)
theorem file95_43465 : (((((p4 ∨ True) ∨ (False → False)) ∨ ((True → p7) ∨ (p4 ∧ p7))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p4 ∨ True) ∨ (False → False)) ∨ ((True → p7) ∨ (p4 ∧ p7))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p4 p7 p5 p0 : Prop)
theorem file95_43849 : ((((((True → p5) → False) → ((False ∨ p0) ∨ (p7 → True))) ∨ (((p7 ∨ p4) → (p5 ∨ p3)) ∧ ((p4 → False) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((True → p5) → False) → ((False ∨ p0) ∨ (p7 → True))) ∨ (((p7 ∨ p4) → (p5 ∨ p3)) ∧ ((p4 → False) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p2 p1 p7 p0 : Prop)
theorem file95_44366 : ((((((p7 ∧ p5) ∨ (p2 ∨ p1)) → False) → (((p0 ∧ p7) → (p5 → p2)) ∨ ((True → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p7 ∧ p5) ∨ (p2 ∨ p1)) → False) → (((p0 ∧ p7) → (p5 → p2)) ∨ ((True → p0) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      have assump_29 : ((p7 ∧ p5) ∨ (p2 ∨ p1)) := by
        apply Or.inl
        apply And.intro
        exact assump_13
        exact assump_9
      let assump_21 := assump_5 assump_29
      apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p7 p5 p6 p2 p4 p0 p3 p1 : Prop)
theorem file95_45092 : ((((((p4 → False) ∧ (p3 ∧ p4)) ∨ ((False ∧ p5) ∨ (True → False))) → (((p7 ∧ p5) ∧ (p1 → p4)) → ((p5 ∧ p6) ∨ (p0 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_50 : ((((p4 → False) ∧ (p3 ∧ p4)) ∨ ((False ∧ p5) ∨ (True → False))) → (((p7 ∧ p5) ∧ (p1 → p4)) → ((p5 ∧ p6) ∨ (p0 ∧ p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              have assump_51 : p4 := by
                exact assump_24
              let assump_31 := assump_19 assump_51
              apply False.elim assump_31
        case inr assump_18 =>
          cases assump_18
          case inl assump_35 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
          case inr assump_36 =>
            have assump_52 : True := by
              apply True.intro
            let assump_43 := assump_36 assump_52
            apply False.elim assump_43
  let assump_4 := assump_1 assump_50
  apply False.elim assump_4


variable (p7 p0 p1 p5 p4 p2 p3 : Prop)
theorem file95_46434 : (((((True ∧ p1) ∧ (p7 → False)) ∧ ((p1 ∧ p7) → (p4 ∧ False))) ∧ (((p1 ∨ p0) → False) → ((p4 ∧ p2) → (p5 → p5)))) → ((((p4 ∧ p3) ∧ (False → False)) → ((p4 → False) → False)) ∨ (((p5 ∧ p5) → (p0 → False)) ∧ ((p3 → False) ∧ (p7 ∨ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply Or.inl
          intro assump_20
          intro assump_21
          cases assump_20
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              have assump_41 : p4 := by
                exact assump_26
              let assump_37 := assump_21 assump_41
              apply False.elim assump_37


variable (p6 p5 p2 p1 p3 p7 : Prop)
theorem file95_47363 : ((((((p3 → False) ∧ (p2 → p1)) → ((False ∨ p7) → (p5 ∧ p3))) → (((p3 ∨ True) → (p1 → False)) → ((p6 ∨ False) → (p2 ∨ p6)))) → False) → False) := by
  intro assump_5
  have assump_25 : ((((p3 → False) ∧ (p2 → p1)) → ((False ∨ p7) → (p5 ∧ p3))) → (((p3 ∨ True) → (p1 → False)) → ((p6 ∨ False) → (p2 ∨ p6)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      apply Or.inr
      exact assump_12
    case inr assump_13 =>
      apply False.elim assump_13
  let assump_8 := assump_5 assump_25
  apply False.elim assump_8


variable (p6 p3 p4 p7 p2 : Prop)
theorem file95_48002 : (((((p7 ∨ p2) ∧ (p6 ∨ False)) → ((p3 → False) → False)) ∧ (((True ∨ True) ∨ (False → True)) → ((p7 → p6) → False))) → ((((p6 ∨ p7) → False) → False) ∨ (((p3 ∧ p2) ∧ (p4 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_25 : ((True ∨ True) ∨ (False → True)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_12 := assump_3 assump_25
    have assump_26 : (p7 → p6) := by
      intro assump_14
      have assump_27 : (p6 ∨ p7) := by
        apply Or.inr
        exact assump_14
      let assump_18 := assump_8 assump_27
      apply False.elim assump_18
    let assump_13 := assump_12 assump_26
    apply False.elim assump_13


variable (p0 p6 : Prop)
theorem file95_48801 : ((((((p0 ∧ False) → (p6 → True)) → False) → False) → False) → False) := by
  intro assump_18
  have assump_34 : ((((p0 ∧ False) → (p6 → True)) → False) → False) := by
    intro assump_22
    have assump_35 : ((p0 ∧ False) → (p6 → True)) := by
      intro assump_26
      intro assump_27
      apply True.intro
    let assump_25 := assump_22 assump_35
    apply False.elim assump_25
  let assump_21 := assump_18 assump_34
  apply False.elim assump_21


variable (p2 p3 p0 p7 p4 p6 p5 : Prop)
theorem file95_49314 : (((((False → p2) ∨ (p6 → p0)) ∧ ((False ∧ p3) ∧ (True ∧ p7))) ∧ (((p3 ∨ True) → (True → True)) → False)) → ((((p6 ∧ p0) → (p5 → False)) → False) ∨ (((p7 ∨ p0) → (p7 ∧ p3)) ∧ ((p5 ∧ p4) → False)))) := by
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
            apply False.elim assump_12
      case inr assump_7 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20


variable (p3 p5 p4 p6 p1 p7 p2 p0 : Prop)
theorem file95_50129 : (((((True ∧ p3) ∨ (p5 ∨ False)) ∨ ((p4 ∧ p4) → (p1 ∨ True))) ∨ (((p6 → p6) → False) ∨ ((p7 ∨ True) ∧ (False ∧ p0)))) ∧ ((((p7 → p7) ∧ (False → False)) ∨ ((p0 ∨ False) → (p5 → False))) ∨ (((p2 ∨ p5) → (p3 ∨ p7)) ∧ ((p5 ∧ True) → (p2 ∧ False))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    apply True.intro
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_8
  exact assump_8
  intro assump_11
  apply False.elim assump_11


variable (p6 p2 p0 p3 p4 p7 p5 p1 : Prop)
theorem file95_50729 : (((((p4 → True) ∧ (p2 → p7)) → False) → (((True ∧ p1) → (p7 ∧ p7)) → ((p7 ∧ False) → False))) ∨ ((((p1 → False) → False) ∧ ((p4 ∧ p0) → (p2 ∧ p3))) → (((p5 ∨ p6) → False) ∧ ((p2 ∧ False) ∧ (p1 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5


variable (p3 p6 p0 p5 p2 p4 : Prop)
theorem file95_51148 : ((((((p5 ∧ p2) → False) ∧ ((p6 → False) ∧ (False ∧ p4))) → (((p6 → False) ∨ (p0 ∧ p4)) ∨ ((p0 → False) ∨ (p0 → p3)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p5 ∧ p2) → False) ∧ ((p6 → False) ∧ (False ∧ p4))) → (((p6 → False) ∨ (p0 ∧ p4)) ∨ ((p0 → False) ∨ (p0 → p3)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p1 p6 p5 p4 p3 p2 : Prop)
theorem file95_51814 : (((((True → True) → False) → False) ∧ (((True → p0) ∨ (p2 → False)) → ((p5 → True) ∨ (p6 ∧ p1)))) ∨ ((((p3 ∧ p1) → False) ∨ ((p2 → False) → (p1 ∧ False))) ∨ (((p1 → p5) ∨ (p1 → False)) → ((p4 → p1) ∨ (p5 → False))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_18 : (True → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    apply Or.inl
    intro assump_14
    apply True.intro
  case inr assump_11 =>
    apply Or.inl
    intro assump_17
    apply True.intro


variable (p1 p2 p3 p6 p4 p7 p5 : Prop)
theorem file95_52492 : (((((p1 → False) ∧ (p4 ∧ p6)) → ((False ∧ p3) ∨ (p3 ∨ p4))) → False) → ((((False ∨ p5) ∨ (p1 ∧ p6)) → ((p7 → p2) ∨ (True → False))) → (((p7 ∧ p3) → (p6 ∨ p1)) ∨ ((False ∧ p1) → (p2 → True))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_31 : (((p1 → False) ∧ (p4 ∧ p6)) → ((False ∧ p3) ∨ (p3 ∨ p4))) := by
      intro assump_17
      cases assump_17
      case intro assump_18 assump_19 =>
        cases assump_19
        case intro assump_22 assump_23 =>
          apply Or.inr
          apply Or.inl
          exact assump_9
    let assump_16 := assump_1 assump_31
    apply False.elim assump_16


variable (p6 p5 p4 p0 p7 p1 : Prop)
theorem file95_53245 : ((((((p6 → p5) ∧ (p4 → False)) ∧ ((True ∨ p0) → False)) → (((p1 ∧ p6) → (p7 → False)) ∨ ((p7 ∧ False) → False))) → False) → False) := by
  intro assump_7
  have assump_42 : ((((p6 → p5) ∧ (p4 → False)) ∧ ((True ∨ p0) → False)) → (((p1 ∧ p6) → (p7 → False)) ∨ ((p7 ∧ False) → False))) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply Or.inl
        intro assump_22
        intro assump_23
        cases assump_22
        case intro assump_26 assump_27 =>
          have assump_43 : (True ∨ p0) := by
            apply Or.inl
            apply True.intro
          let assump_35 := assump_13 assump_43
          apply False.elim assump_35
  let assump_10 := assump_7 assump_42
  apply False.elim assump_10


variable (p7 p6 p3 p0 p5 p1 p4 : Prop)
theorem file95_54123 : ((((((p1 ∨ True) → False) ∧ ((p5 ∨ p7) ∧ (False → False))) → (((p7 ∧ p6) ∧ (True ∨ p0)) → ((p3 ∧ p4) → (p4 ∧ True)))) → False) → False) := by
  intro assump_34
  have assump_96 : ((((p1 ∨ True) → False) ∧ ((p5 ∨ p7) ∧ (False → False))) → (((p7 ∧ p6) ∧ (True ∨ p0)) → ((p3 ∧ p4) → (p4 ∧ True)))) := by
    intro assump_38
    intro assump_39
    intro assump_40
    apply And.intro
    cases assump_40
    case intro assump_41 assump_42 =>
      cases assump_39
      case intro assump_47 assump_48 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          cases assump_48
          case inl assump_55 =>
            cases assump_38
            case intro assump_59 assump_60 =>
              cases assump_60
              case intro assump_63 assump_64 =>
                cases assump_63
                case inl assump_65 =>
                  exact assump_42
                case inr assump_66 =>
                  exact assump_42
          case inr assump_56 =>
            cases assump_38
            case intro assump_77 assump_78 =>
              cases assump_78
              case intro assump_81 assump_82 =>
                cases assump_81
                case inl assump_83 =>
                  exact assump_42
                case inr assump_84 =>
                  exact assump_42
    apply True.intro
  let assump_37 := assump_34 assump_96
  apply False.elim assump_37


variable (p4 p5 : Prop)
theorem file95_55573 : ((((((p4 ∨ p5) ∨ (p4 → p5)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 ∨ p5) ∨ (p4 → p5)) → False) → False) := by
    intro assump_5
    have assump_24 : ((p4 ∨ p5) ∨ (p4 → p5)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((p4 ∨ p5) ∨ (p4 → p5)) := by
        apply Or.inl
        apply Or.inl
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p4 p0 p6 p5 p1 : Prop)
theorem file95_56226 : ((((((True → False) ∧ (p4 ∨ p3)) ∧ ((p6 → False) ∨ (p0 ∨ p5))) → False) → ((((True ∨ p5) → (True ∨ p6)) → False) ∧ (((p6 → False) ∧ (False → p1)) ∨ ((p0 ∨ p3) ∧ (p1 ∨ p1))))) → False) := by
  intro assump_1
  have assump_86 : ((((True → False) ∧ (p4 ∨ p3)) ∧ ((p6 → False) ∨ (p0 ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_7
          case inl assump_16 =>
            have assump_87 : True := by
              apply True.intro
            let assump_22 := assump_8 assump_87
            apply False.elim assump_22
          case inr assump_17 =>
            cases assump_17
            case inl assump_26 =>
              have assump_88 : True := by
                apply True.intro
              let assump_32 := assump_8 assump_88
              apply False.elim assump_32
            case inr assump_27 =>
              have assump_89 : True := by
                apply True.intro
              let assump_40 := assump_8 assump_89
              apply False.elim assump_40
        case inr assump_13 =>
          cases assump_7
          case inl assump_46 =>
            have assump_90 : True := by
              apply True.intro
            let assump_52 := assump_8 assump_90
            apply False.elim assump_52
          case inr assump_47 =>
            cases assump_47
            case inl assump_56 =>
              have assump_91 : True := by
                apply True.intro
              let assump_62 := assump_8 assump_91
              apply False.elim assump_62
            case inr assump_57 =>
              have assump_92 : True := by
                apply True.intro
              let assump_70 := assump_8 assump_92
              apply False.elim assump_70
  let assump_4 := assump_1 assump_86
  let assump_74 := And.left assump_4
  have assump_93 : ((True ∨ p5) → (True ∨ p6)) := by
    intro assump_76
    cases assump_76
    case inl assump_77 =>
      apply Or.inl
      apply True.intro
    case inr assump_78 =>
      apply Or.inl
      apply True.intro
  let assump_75 := assump_74 assump_93
  apply False.elim assump_75


variable (p1 p2 p7 p3 : Prop)
theorem file95_58519 : (((((p7 ∨ p3) → False) ∧ ((False → False) ∨ (p3 ∨ True))) ∧ (((p1 → False) → False) ∧ ((p2 ∨ p1) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_90 : True := by
                apply True.intro
              let assump_24 := assump_17 assump_90
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_91 : True := by
                apply True.intro
              let assump_32 := assump_17 assump_91
              apply False.elim assump_32
      case inr assump_9 =>
        cases assump_9
        case inl assump_36 =>
          cases assump_3
          case intro assump_40 assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              cases assump_44
              case inl assump_46 =>
                have assump_92 : True := by
                  apply True.intro
                let assump_52 := assump_45 assump_92
                apply False.elim assump_52
              case inr assump_47 =>
                have assump_93 : True := by
                  apply True.intro
                let assump_60 := assump_45 assump_93
                apply False.elim assump_60
        case inr assump_37 =>
          cases assump_3
          case intro assump_66 assump_67 =>
            cases assump_67
            case intro assump_70 assump_71 =>
              cases assump_70
              case inl assump_72 =>
                have assump_94 : True := by
                  apply True.intro
                let assump_78 := assump_71 assump_94
                apply False.elim assump_78
              case inr assump_73 =>
                have assump_95 : True := by
                  apply True.intro
                let assump_86 := assump_71 assump_95
                apply False.elim assump_86


variable (p5 p2 p6 p4 p7 p0 p1 : Prop)
theorem file95_60750 : ((((((p4 ∧ p1) → (p1 ∧ p4)) → False) → False) ∧ ((((p5 → p7) ∨ (p6 ∧ p2)) → False) ∧ (((p4 ∧ p0) ∨ (p4 ∧ p2)) ∧ ((p4 ∨ p5) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_38 : (p4 ∨ p5) := by
              apply Or.inl
              exact assump_14
            let assump_22 := assump_11 assump_38
            apply False.elim assump_22
        case inr assump_13 =>
          cases assump_13
          case intro assump_26 assump_27 =>
            have assump_39 : (p4 ∨ p5) := by
              apply Or.inl
              exact assump_26
            let assump_34 := assump_11 assump_39
            apply False.elim assump_34


variable (p6 p1 p0 p5 p2 p7 p4 p3 : Prop)
theorem file95_61754 : (((((p4 ∨ p2) ∨ (p4 ∨ True)) → ((p0 ∨ p7) ∧ (p0 → True))) → (((p4 ∨ p7) ∧ (p5 ∧ p5)) ∨ ((p5 ∧ p5) → (p7 ∨ True)))) ∨ ((((p6 → p5) ∧ (p3 ∧ p2)) ∨ ((p4 → True) ∧ (p4 ∨ p1))) ∧ (((p5 ∨ p1) ∨ (p6 ∧ p2)) → ((p0 → False) ∧ (p0 → False))))) := by
  apply Or.inl
  intro assump_12
  apply Or.inr
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    apply Or.inr
    apply True.intro


variable (p6 p0 p1 p2 p7 : Prop)
theorem file95_62209 : (((((p7 ∧ p7) → False) ∧ ((p6 → p7) ∧ (p7 ∨ p0))) ∧ (((p1 → True) ∧ (p6 → False)) ∧ ((p0 → False) ∧ (p2 → p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                have assump_61 : (p7 ∧ p7) := by
                  apply And.intro
                  exact assump_12
                  exact assump_12
                let assump_36 := assump_4 assump_61
                apply False.elim assump_36
        case inr assump_13 =>
          cases assump_3
          case intro assump_42 assump_43 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              cases assump_43
              case intro assump_50 assump_51 =>
                have assump_62 : p0 := by
                  exact assump_13
                let assump_57 := assump_50 assump_62
                apply False.elim assump_57


variable (p5 p4 p2 p3 p6 p0 p1 : Prop)
theorem file95_63525 : (((((p4 ∧ p2) ∧ (p2 → False)) ∧ ((p2 → p6) ∧ (p6 ∨ p1))) ∧ (((False ∨ p0) ∧ (p3 → False)) → ((p4 ∨ p1) ∨ (p5 → p2)))) ∨ ((((p1 → False) → False) → ((True ∨ p2) ∨ (p5 ∧ p5))) ∧ (((p4 ∧ False) ∧ (p2 → False)) → False))) := by
  apply Or.inr
  apply And.intro
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p4 : Prop)
theorem file95_64048 : ((((((p4 ∨ True) ∨ (True → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 ∨ True) ∨ (True → False)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p4 ∨ True) ∨ (True → False)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p2 p0 p7 p4 : Prop)
theorem file95_64547 : (((((p5 ∨ p2) ∧ (p0 ∨ p0)) → ((p7 → p5) ∨ (p4 ∨ False))) ∧ (((True → False) ∧ (p4 ∨ p0)) ∧ ((p4 → p4) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          have assump_42 : (p4 → p4) := by
            intro assump_25
            exact assump_25
          let assump_24 := assump_13 assump_42
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_43 : (p4 → p4) := by
            intro assump_36
            exact assump_36
          let assump_35 := assump_13 assump_43
          apply False.elim assump_35


variable (p5 p1 p2 p4 p7 p0 : Prop)
theorem file95_65372 : (((((True → False) → False) ∨ ((p7 → False) ∧ (p7 → False))) ∨ (((p2 ∧ p1) ∧ (p4 ∨ True)) ∨ ((p7 → False) → False))) ∨ ((((p0 → False) → (True ∧ p5)) ∨ ((p7 → p5) → (p5 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p5 p1 p3 p7 : Prop)
theorem file95_65801 : ((((((p1 → p5) ∧ (p3 ∨ p4)) → False) → False) ∧ ((((p1 → False) ∧ (p7 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p1 → False) ∧ (p7 ∧ False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p4 p2 p6 p5 p1 p0 p7 p3 : Prop)
theorem file95_66370 : (((((p1 ∧ p6) → False) → False) ∨ (((p0 → True) ∨ (p4 → False)) ∨ ((p7 → p5) → (p6 ∧ p7)))) → ((((False → p3) ∨ (p4 → False)) ∨ ((p6 ∨ False) ∧ (p4 → p5))) ∨ (((p4 ∧ p1) → (p2 → False)) → ((p2 → False) ∧ (p2 ∧ True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        intro assump_15
        apply False.elim assump_15
      case inr assump_12 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        intro assump_20
        apply False.elim assump_20
    case inr assump_10 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      intro assump_25
      apply False.elim assump_25


variable (p2 p7 p4 p6 p0 p3 p5 p1 : Prop)
theorem file95_67345 : (((((p1 ∨ p0) ∧ (p5 ∨ p5)) ∨ ((p7 → True) ∧ (p7 ∨ True))) → False) → ((((p2 ∨ p5) ∧ (p3 → p6)) ∨ ((False → p2) ∨ (p5 ∨ True))) ∧ (((p5 → True) ∨ (p2 → p1)) → ((p4 ∨ p4) ∧ (p3 → p1))))) := by
  intro assump_22
  apply And.intro
  apply Or.inr
  apply Or.inl
  intro assump_25
  apply False.elim assump_25
  intro assump_28
  apply And.intro
  cases assump_28
  case inl assump_29 =>
    have assump_72 : (((p1 ∨ p0) ∧ (p5 ∨ p5)) ∨ ((p7 → True) ∧ (p7 ∨ True))) := by
      apply Or.inr
      apply And.intro
      intro assump_36
      apply True.intro
      apply Or.inr
      apply True.intro
    let assump_35 := assump_22 assump_72
    apply False.elim assump_35
  case inr assump_30 =>
    have assump_73 : (((p1 ∨ p0) ∧ (p5 ∨ p5)) ∨ ((p7 → True) ∧ (p7 ∨ True))) := by
      apply Or.inr
      apply And.intro
      intro assump_45
      apply True.intro
      apply Or.inr
      apply True.intro
    let assump_44 := assump_22 assump_73
    apply False.elim assump_44
  intro assump_49
  cases assump_28
  case inl assump_52 =>
    have assump_74 : (((p1 ∨ p0) ∧ (p5 ∨ p5)) ∨ ((p7 → True) ∧ (p7 ∨ True))) := by
      apply Or.inr
      apply And.intro
      intro assump_59
      apply True.intro
      apply Or.inr
      apply True.intro
    let assump_58 := assump_22 assump_74
    apply False.elim assump_58
  case inr assump_53 =>
    have assump_75 : (((p1 ∨ p0) ∧ (p5 ∨ p5)) ∨ ((p7 → True) ∧ (p7 ∨ True))) := by
      apply Or.inr
      apply And.intro
      intro assump_68
      apply True.intro
      apply Or.inr
      apply True.intro
    let assump_67 := assump_22 assump_75
    apply False.elim assump_67


variable (p2 p3 p0 p1 : Prop)
theorem file95_69021 : ((((((p1 ∨ p0) → False) → False) → False) ∧ ((((True → False) → False) ∨ ((p2 ∨ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True → False) → False) ∨ ((p2 ∨ p3) → False)) := by
      apply Or.inl
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p1 p5 p3 p2 p7 p6 : Prop)
theorem file95_69590 : (((((p2 ∧ True) ∨ (p6 ∧ p2)) ∧ ((False ∧ p3) → (p5 ∨ p5))) ∨ (((False ∧ p7) → False) → ((p6 → p4) → (False → False)))) ∧ ((((False ∧ p4) ∧ (p4 ∨ p2)) ∧ ((p3 ∧ p1) → (p7 → False))) → False)) := by
  apply And.intro
  apply Or.inr
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p6 p5 p3 p4 p1 p7 : Prop)
theorem file95_70178 : ((((((p6 → True) → False) → ((False → False) ∧ (p5 ∧ p1))) ∨ (((True → False) ∧ (p4 ∧ p7)) ∨ ((p3 ∨ True) ∧ (False ∧ p3)))) → False) → False) := by
  intro assump_10
  have assump_35 : ((((p6 → True) → False) → ((False → False) ∧ (p5 ∧ p1))) ∨ (((True → False) ∧ (p4 ∧ p7)) ∨ ((p3 ∨ True) ∧ (False ∧ p3)))) := by
    apply Or.inl
    intro assump_14
    apply And.intro
    intro assump_15
    apply False.elim assump_15
    apply And.intro
    have assump_36 : (p6 → True) := by
      intro assump_21
      apply True.intro
    let assump_20 := assump_14 assump_36
    apply False.elim assump_20
    have assump_37 : (p6 → True) := by
      intro assump_28
      apply True.intro
    let assump_27 := assump_14 assump_37
    apply False.elim assump_27
  let assump_13 := assump_10 assump_35
  apply False.elim assump_13


variable (p4 p2 p3 p0 p5 p1 p7 p6 : Prop)
theorem file95_71065 : (((((False → False) → (True → False)) → ((p0 ∨ p3) → (p5 ∧ p1))) → False) → ((((p7 ∧ p4) ∧ (p2 → p6)) ∨ ((True → p7) → False)) ∨ (((False → False) → False) ∧ ((False → False) → (p4 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_67 : (((False → False) → (True → False)) → ((p0 ∨ p3) → (p5 ∧ p1))) := by
    intro assump_10
    intro assump_11
    apply And.intro
    cases assump_11
    case inl assump_12 =>
      have assump_68 : (False → False) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_10 assump_68
      have assump_69 : True := by
        apply True.intro
      let assump_22 := assump_18 assump_69
      apply False.elim assump_22
    case inr assump_13 =>
      have assump_70 : (False → False) := by
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_10 assump_70
      have assump_71 : True := by
        apply True.intro
      let assump_34 := assump_30 assump_71
      apply False.elim assump_34
    cases assump_11
    case inl assump_38 =>
      have assump_72 : (False → False) := by
        intro assump_45
        apply False.elim assump_45
      let assump_44 := assump_10 assump_72
      have assump_73 : True := by
        apply True.intro
      let assump_48 := assump_44 assump_73
      apply False.elim assump_48
    case inr assump_39 =>
      have assump_74 : (False → False) := by
        intro assump_57
        apply False.elim assump_57
      let assump_56 := assump_10 assump_74
      have assump_75 : True := by
        apply True.intro
      let assump_60 := assump_56 assump_75
      apply False.elim assump_60
  let assump_9 := assump_1 assump_67
  apply False.elim assump_9


variable (p1 p3 p4 p2 p6 : Prop)
theorem file95_72871 : ((((((True → p4) → (p4 → p6)) → ((p2 → False) ∧ (p1 → False))) → (((p2 ∧ p6) → False) ∨ ((p1 → p3) → (p2 → p4)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True → p4) → (p4 → p6)) → ((p2 → False) ∧ (p1 → False))) → (((p2 ∧ p6) → False) ∨ ((p1 → p3) → (p2 → p4)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_33 : ((True → p4) → (p4 → p6)) := by
        intro assump_18
        intro assump_19
        exact assump_10
      let assump_17 := assump_5 assump_33
      let assump_24 := And.left assump_17
      have assump_34 : p2 := by
        exact assump_9
      let assump_25 := assump_24 assump_34
      apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p0 p7 p2 p6 p4 : Prop)
theorem file95_73741 : (((((True ∨ p0) ∨ (p4 → p7)) → False) → False) ∨ ((((p1 ∨ p7) ∧ (p1 → p0)) → False) ∨ (((True → False) ∨ (p6 → False)) ∨ ((p2 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∨ p0) ∨ (p4 → p7)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p4 p7 p1 p0 p6 p2 : Prop)
theorem file95_74158 : (((((False ∨ p4) → (False ∧ p1)) ∧ ((p2 ∨ True) ∨ (False → False))) ∧ (((p3 ∧ p6) → (p0 ∨ p3)) → False)) → ((((True ∨ False) → False) → False) → (((p7 ∧ False) ∨ (False ∨ False)) → ((p3 ∨ p3) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_3
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    case inr assump_10 =>
      cases assump_10
      case inl assump_17 =>
        apply False.elim assump_17
      case inr assump_18 =>
        apply False.elim assump_18
  case inr assump_6 =>
    cases assump_3
    case inl assump_25 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_28
    case inr assump_26 =>
      cases assump_26
      case inl assump_33 =>
        apply False.elim assump_33
      case inr assump_34 =>
        apply False.elim assump_34


variable (p3 p4 p6 p2 p0 p1 p5 p7 : Prop)
theorem file95_75195 : (((((p6 → p0) ∨ (p7 → False)) ∨ ((False → False) → False)) ∨ (((p7 → p4) ∧ (p7 → p7)) ∨ ((p7 ∧ p6) ∧ (p1 ∧ p7)))) → ((((p2 ∨ p5) ∨ (p4 → True)) ∨ ((p0 ∨ False) → (p5 ∧ p3))) → (((p0 → False) → (False → False)) ∨ ((p4 → False) ∨ (p7 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case inl assump_11 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_13
            case inl assump_15 =>
              apply Or.inl
              intro assump_19
              intro assump_20
              apply False.elim assump_20
            case inr assump_16 =>
              apply Or.inl
              intro assump_25
              intro assump_26
              apply False.elim assump_26
          case inr assump_14 =>
            apply Or.inl
            intro assump_31
            intro assump_32
            apply False.elim assump_32
        case inr assump_12 =>
          cases assump_12
          case inl assump_35 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              apply Or.inl
              intro assump_43
              intro assump_44
              apply False.elim assump_44
          case inr assump_36 =>
            cases assump_36
            case intro assump_47 assump_48 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                cases assump_48
                case intro assump_55 assump_56 =>
                  apply Or.inl
                  intro assump_61
                  intro assump_62
                  apply False.elim assump_62
      case inr assump_8 =>
        cases assump_1
        case inl assump_67 =>
          cases assump_67
          case inl assump_69 =>
            cases assump_69
            case inl assump_71 =>
              apply Or.inl
              intro assump_75
              intro assump_76
              apply False.elim assump_76
            case inr assump_72 =>
              apply Or.inl
              intro assump_81
              intro assump_82
              apply False.elim assump_82
          case inr assump_70 =>
            apply Or.inl
            intro assump_87
            intro assump_88
            apply False.elim assump_88
        case inr assump_68 =>
          cases assump_68
          case inl assump_91 =>
            cases assump_91
            case intro assump_93 assump_94 =>
              apply Or.inl
              intro assump_99
              intro assump_100
              apply False.elim assump_100
          case inr assump_92 =>
            cases assump_92
            case intro assump_103 assump_104 =>
              cases assump_103
              case intro assump_105 assump_106 =>
                cases assump_104
                case intro assump_111 assump_112 =>
                  apply Or.inl
                  intro assump_117
                  intro assump_118
                  apply False.elim assump_118
    case inr assump_6 =>
      cases assump_1
      case inl assump_123 =>
        cases assump_123
        case inl assump_125 =>
          cases assump_125
          case inl assump_127 =>
            apply Or.inl
            intro assump_131
            intro assump_132
            apply False.elim assump_132
          case inr assump_128 =>
            apply Or.inl
            intro assump_137
            intro assump_138
            apply False.elim assump_138
        case inr assump_126 =>
          apply Or.inl
          intro assump_143
          intro assump_144
          apply False.elim assump_144
      case inr assump_124 =>
        cases assump_124
        case inl assump_147 =>
          cases assump_147
          case intro assump_149 assump_150 =>
            apply Or.inl
            intro assump_155
            intro assump_156
            apply False.elim assump_156
        case inr assump_148 =>
          cases assump_148
          case intro assump_159 assump_160 =>
            cases assump_159
            case intro assump_161 assump_162 =>
              cases assump_160
              case intro assump_167 assump_168 =>
                apply Or.inl
                intro assump_173
                intro assump_174
                apply False.elim assump_174
  case inr assump_4 =>
    cases assump_1
    case inl assump_179 =>
      cases assump_179
      case inl assump_181 =>
        cases assump_181
        case inl assump_183 =>
          apply Or.inl
          intro assump_187
          intro assump_188
          apply False.elim assump_188
        case inr assump_184 =>
          apply Or.inl
          intro assump_193
          intro assump_194
          apply False.elim assump_194
      case inr assump_182 =>
        apply Or.inl
        intro assump_199
        intro assump_200
        apply False.elim assump_200
    case inr assump_180 =>
      cases assump_180
      case inl assump_203 =>
        cases assump_203
        case intro assump_205 assump_206 =>
          apply Or.inl
          intro assump_211
          intro assump_212
          apply False.elim assump_212
      case inr assump_204 =>
        cases assump_204
        case intro assump_215 assump_216 =>
          cases assump_215
          case intro assump_217 assump_218 =>
            cases assump_216
            case intro assump_223 assump_224 =>
              apply Or.inl
              intro assump_229
              intro assump_230
              apply False.elim assump_230


variable (p7 p4 p6 p2 p0 p3 : Prop)
theorem file95_80853 : ((((((True ∨ p0) → False) ∨ ((p7 ∨ True) ∧ (p2 → False))) → (((p7 → p4) → (p7 → True)) ∨ ((p6 ∧ p3) → (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((True ∨ p0) → False) ∨ ((p7 ∨ True) ∧ (p2 → False))) → (((p7 → p4) → (p7 → True)) ∨ ((p6 ∧ p3) → (p7 ∨ True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          apply Or.inl
          intro assump_20
          intro assump_21
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 p2 p3 p7 p1 p6 p0 : Prop)
theorem file95_81802 : (((((False → False) → (p6 ∧ p1)) ∧ ((p0 ∨ True) → (True → False))) → False) ∨ ((((p5 ∧ True) → (p6 ∨ p2)) ∨ ((True → p7) ∧ (p7 → False))) → (((p6 ∨ p3) → (p2 → p0)) → ((p6 → False) ∨ (p6 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_13
    have assump_14 : True := by
      apply True.intro
    let assump_9 := assump_8 assump_14
    apply False.elim assump_9


variable (p7 p6 p2 p4 p0 p3 p5 : Prop)
theorem file95_82395 : (((((p3 ∧ p6) → (True ∧ p5)) ∨ ((p0 → p5) ∨ (p6 ∧ p7))) ∧ (((False → False) → (p5 → True)) → ((p0 → p4) ∧ (p0 → False)))) → ((((p2 ∨ True) → False) → ((p0 ∧ False) ∨ (p5 → False))) ∨ (((True ∧ p5) → False) ∨ ((p6 ∨ p4) → (p4 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      apply Or.inr
      intro assump_13
      have assump_57 : (p2 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_17 := assump_10 assump_57
      apply False.elim assump_17
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        apply Or.inl
        intro assump_27
        apply Or.inr
        intro assump_30
        have assump_58 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_34 := assump_27 assump_58
        apply False.elim assump_34
      case inr assump_22 =>
        cases assump_22
        case intro assump_38 assump_39 =>
          apply Or.inl
          intro assump_46
          apply Or.inr
          intro assump_49
          have assump_59 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_53 := assump_46 assump_59
          apply False.elim assump_53


variable (p1 p6 p2 p3 : Prop)
theorem file95_83759 : ((((((p6 ∨ p6) → (p6 → p2)) → False) → (((p1 → True) ∧ (p3 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p6 ∨ p6) → (p6 → p2)) → False) → (((p1 → True) ∧ (p3 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p6 p0 p1 p5 p2 p7 p4 p3 : Prop)
theorem file95_84301 : (((((p0 → False) ∧ (p4 ∧ p1)) → ((True → p2) → (p5 → False))) → (((False ∨ False) ∧ (p6 ∧ p3)) → False)) ∨ ((((p7 ∨ p4) ∧ (p1 ∨ p2)) ∧ ((p0 → p5) ∧ (True → False))) ∧ (((False ∧ p4) → (p1 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      apply False.elim assump_6


variable (p6 p5 p4 p1 p3 : Prop)
theorem file95_84805 : ((((((p3 → p4) ∨ (p1 ∧ p5)) ∧ ((False → False) ∧ (p6 ∧ p6))) ∨ (((p4 → True) → False) → False)) ∧ ((((p3 ∨ True) ∨ (p1 ∧ p3)) ∨ ((p5 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            cases assump_13
            case intro assump_16 assump_17 =>
              have assump_58 : (((p3 ∨ True) ∨ (p1 ∧ p3)) ∨ ((p5 → False) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_24 := assump_3 assump_58
              apply False.elim assump_24
        case inr assump_9 =>
          cases assump_9
          case intro assump_28 assump_29 =>
            cases assump_7
            case intro assump_34 assump_35 =>
              cases assump_35
              case intro assump_38 assump_39 =>
                have assump_59 : (((p3 ∨ True) ∨ (p1 ∧ p3)) ∨ ((p5 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inr
                  apply True.intro
                let assump_46 := assump_3 assump_59
                apply False.elim assump_46
    case inr assump_5 =>
      have assump_60 : (((p3 ∨ True) ∨ (p1 ∧ p3)) ∨ ((p5 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_54 := assump_3 assump_60
      apply False.elim assump_54


variable (p7 p5 p4 p1 p2 p6 p0 : Prop)
theorem file95_86546 : (((((p4 ∨ p0) ∨ (p1 → False)) ∧ ((p4 → p5) ∧ (False ∧ p1))) ∧ (((False ∧ p6) ∨ (True → False)) → ((True → False) → (p5 → False)))) → ((((False ∧ p1) ∧ (p6 ∨ False)) → ((True ∨ True) ∧ (p2 ∨ p5))) → (((p4 → p7) ∨ (p4 → p2)) ∨ ((p7 ∧ p5) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_8
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
        case inr assump_12 =>
          cases assump_8
          case intro assump_25 assump_26 =>
            cases assump_26
            case intro assump_29 assump_30 =>
              apply False.elim assump_29
      case inr assump_10 =>
        cases assump_8
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            apply False.elim assump_39


variable (p5 p2 p0 p1 p7 p4 p6 : Prop)
theorem file95_87704 : ((((((False ∧ p0) → (p6 ∧ p2)) ∨ ((p0 → False) → False)) ∧ (((p5 → p0) ∨ (p4 → False)) → ((p7 → p6) → (p2 → p7)))) ∧ ((((p6 ∧ p1) ∧ (p2 ∨ p2)) ∧ ((p6 → False) ∧ (p2 ∧ p2))) ∧ (((p0 ∨ True) → (p0 → True)) ∧ ((p5 ∨ p2) → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_21
                case inl assump_28 =>
                  cases assump_19
                  case intro assump_32 assump_33 =>
                    cases assump_33
                    case intro assump_36 assump_37 =>
                      cases assump_17
                      case intro assump_42 assump_43 =>
                        have assump_136 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_37
                        let assump_48 := assump_43 assump_136
                        apply False.elim assump_48
                case inr assump_29 =>
                  cases assump_19
                  case intro assump_54 assump_55 =>
                    cases assump_55
                    case intro assump_58 assump_59 =>
                      cases assump_17
                      case intro assump_64 assump_65 =>
                        have assump_137 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_59
                        let assump_70 := assump_65 assump_137
                        apply False.elim assump_70
      case inr assump_11 =>
        cases assump_7
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            cases assump_80
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                cases assump_83
                case inl assump_90 =>
                  cases assump_81
                  case intro assump_94 assump_95 =>
                    cases assump_95
                    case intro assump_98 assump_99 =>
                      cases assump_79
                      case intro assump_104 assump_105 =>
                        have assump_138 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_99
                        let assump_110 := assump_105 assump_138
                        apply False.elim assump_110
                case inr assump_91 =>
                  cases assump_81
                  case intro assump_116 assump_117 =>
                    cases assump_117
                    case intro assump_120 assump_121 =>
                      cases assump_79
                      case intro assump_126 assump_127 =>
                        have assump_139 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_121
                        let assump_132 := assump_127 assump_139
                        apply False.elim assump_132


variable (p0 p4 p6 p2 p5 p7 p1 : Prop)
theorem file95_91105 : (((((p6 ∨ p1) ∨ (p6 ∧ p7)) ∧ ((p7 ∧ p4) → False)) → (((p2 ∨ p5) → False) → ((p7 ∨ p6) ∨ (False → False)))) ∨ ((((p0 → False) → (p2 → False)) ∧ ((p7 → False) ∨ (p7 ∧ p6))) → (((p4 ∨ p1) ∧ (True ∨ p6)) ∧ ((p0 → p5) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        apply Or.inr
        exact assump_9
      case inr assump_10 =>
        apply Or.inr
        intro assump_19
        apply False.elim assump_19
    case inr assump_8 =>
      cases assump_8
      case intro assump_22 assump_23 =>
        apply Or.inl
        apply Or.inl
        exact assump_23


variable (p4 p0 p1 p3 p6 p5 p2 : Prop)
theorem file95_91916 : (((((True ∨ p5) → False) ∧ ((True ∨ p4) ∧ (p0 ∨ p6))) → False) ∧ ((((p5 → True) → False) → False) ∨ (((p1 → p3) ∨ (p2 → p5)) → False))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          have assump_56 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_17 := assump_2 assump_56
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_57 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_24 := assump_2 assump_57
          apply False.elim assump_24
      case inr assump_9 =>
        cases assump_7
        case inl assump_30 =>
          have assump_58 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_36 := assump_2 assump_58
          apply False.elim assump_36
        case inr assump_31 =>
          have assump_59 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_44 := assump_2 assump_59
          apply False.elim assump_44
  apply Or.inl
  intro assump_48
  have assump_60 : (p5 → True) := by
    intro assump_52
    apply True.intro
  let assump_51 := assump_48 assump_60
  apply False.elim assump_51


variable (p3 p4 p7 p0 p5 p2 p1 : Prop)
theorem file95_93410 : (((((p2 ∧ p1) → False) → False) → (((p7 ∧ p0) ∨ (p7 ∨ p3)) → ((p3 ∨ True) ∨ (p7 → False)))) ∨ ((((True → True) → (p3 ∨ p2)) ∨ ((p2 → p3) → False)) → (((p5 ∧ p7) ∨ (p4 ∧ p1)) ∧ ((p0 ∧ p1) → (p7 → p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_4 =>
    cases assump_4
    case inl assump_13 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_14 =>
      apply Or.inl
      apply Or.inl
      exact assump_14


variable (p5 p7 p3 p4 p6 p0 p1 p2 : Prop)
theorem file95_94105 : (((((True → True) → False) ∧ ((p3 ∧ True) → (False → False))) → False) ∨ ((((p7 ∨ False) ∨ (p0 ∧ p0)) → ((p0 → p3) → (p7 ∨ p1))) → (((p5 → p2) → False) ∨ ((p3 ∧ p4) ∧ (p6 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : (True → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_2 assump_14
    apply False.elim assump_9


variable (p7 p3 p1 p0 p6 p5 p4 p2 : Prop)
theorem file95_94596 : (((((True → False) ∧ (p7 ∧ p7)) → False) ∨ (((p7 ∧ p6) → (p6 ∧ p6)) → ((p7 ∨ p1) ∧ (p6 → False)))) ∨ ((((p4 → True) → (p2 ∧ p6)) → ((p5 ∨ p0) ∧ (p0 ∨ p2))) → (((p3 → False) → False) → ((p3 ∧ False) ∧ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : True := by
        apply True.intro
      let assump_14 := assump_2 assump_18
      apply False.elim assump_14


variable (p1 p7 : Prop)
theorem file95_95157 : ((((((p7 ∨ True) ∨ (p1 ∧ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∨ True) ∨ (p1 ∧ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p7 ∨ True) ∨ (p1 ∧ True)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p3 p2 p0 : Prop)
theorem file95_95644 : ((((((p3 → False) ∧ (p3 ∧ p7)) ∧ ((p2 → True) → (p0 → False))) → (((p2 ∧ p0) ∧ (p0 → False)) ∨ ((True → False) ∨ (p2 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 → False) ∧ (p3 ∧ p7)) ∧ ((p2 → True) → (p0 → False))) → (((p2 ∧ p0) ∧ (p0 → False)) ∨ ((True → False) ∨ (p2 ∨ False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inr
          apply Or.inl
          intro assump_20
          have assump_36 : p3 := by
            exact assump_12
          let assump_28 := assump_8 assump_36
          apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p6 p2 p5 p1 p3 p4 p0 p7 : Prop)
theorem file95_96514 : (((((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) → (((p2 → True) → False) ∨ ((True → False) ∧ (p0 ∧ False)))) → ((((p2 → p0) → False) → ((p2 → p0) ∨ (p1 ∨ True))) → (((p7 → False) ∨ (p0 ∧ p6)) ∧ ((True ∨ p4) → False)))) := by
  intro assump_23
  intro assump_24
  apply And.intro
  apply Or.inl
  intro assump_29
  have assump_202 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
    apply Or.inr
    intro assump_34
    cases assump_34
    case intro assump_35 assump_36 =>
      have assump_203 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        exact assump_36
      let assump_44 := assump_23 assump_203
      cases assump_44
      case inl assump_46 =>
        have assump_204 : (p2 → True) := by
          intro assump_51
          apply True.intro
        let assump_50 := assump_46 assump_204
        apply False.elim assump_50
      case inr assump_47 =>
        cases assump_47
        case intro assump_55 assump_56 =>
          cases assump_56
          case intro assump_59 assump_60 =>
            apply False.elim assump_60
  let assump_33 := assump_23 assump_202
  cases assump_33
  case inl assump_66 =>
    have assump_205 : (p2 → True) := by
      intro assump_71
      apply True.intro
    let assump_70 := assump_66 assump_205
    apply False.elim assump_70
  case inr assump_67 =>
    cases assump_67
    case intro assump_75 assump_76 =>
      cases assump_76
      case intro assump_79 assump_80 =>
        apply False.elim assump_80
  intro assump_85
  cases assump_85
  case inl assump_86 =>
    have assump_206 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
      apply Or.inr
      intro assump_95
      cases assump_95
      case intro assump_96 assump_97 =>
        have assump_207 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_97
        let assump_104 := assump_23 assump_207
        cases assump_104
        case inl assump_106 =>
          have assump_208 : (p2 → True) := by
            intro assump_111
            apply True.intro
          let assump_110 := assump_106 assump_208
          apply False.elim assump_110
        case inr assump_107 =>
          cases assump_107
          case intro assump_115 assump_116 =>
            cases assump_116
            case intro assump_119 assump_120 =>
              apply False.elim assump_120
    let assump_94 := assump_23 assump_206
    cases assump_94
    case inl assump_126 =>
      have assump_209 : (p2 → True) := by
        intro assump_131
        apply True.intro
      let assump_130 := assump_126 assump_209
      apply False.elim assump_130
    case inr assump_127 =>
      cases assump_127
      case intro assump_135 assump_136 =>
        cases assump_136
        case intro assump_139 assump_140 =>
          apply False.elim assump_140
  case inr assump_87 =>
    have assump_210 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
      apply Or.inr
      intro assump_152
      cases assump_152
      case intro assump_153 assump_154 =>
        have assump_211 : (((p5 ∧ p3) ∨ (p1 ∨ p6)) ∨ ((p4 ∧ p1) → (p0 ∨ p5))) := by
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_154
        let assump_161 := assump_23 assump_211
        cases assump_161
        case inl assump_163 =>
          have assump_212 : (p2 → True) := by
            intro assump_168
            apply True.intro
          let assump_167 := assump_163 assump_212
          apply False.elim assump_167
        case inr assump_164 =>
          cases assump_164
          case intro assump_172 assump_173 =>
            cases assump_173
            case intro assump_176 assump_177 =>
              apply False.elim assump_177
    let assump_151 := assump_23 assump_210
    cases assump_151
    case inl assump_183 =>
      have assump_213 : (p2 → True) := by
        intro assump_188
        apply True.intro
      let assump_187 := assump_183 assump_213
      apply False.elim assump_187
    case inr assump_184 =>
      cases assump_184
      case intro assump_192 assump_193 =>
        cases assump_193
        case intro assump_196 assump_197 =>
          apply False.elim assump_197


variable (p3 p1 p4 p2 : Prop)
theorem file95_100893 : (((((p4 ∨ p3) ∧ (p1 → False)) → ((p2 → True) ∨ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p4 ∨ p3) ∧ (p1 → False)) → ((p2 → True) ∨ (p1 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        intro assump_19
        apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p4 p6 p2 : Prop)
theorem file95_101489 : (((((True → False) → (p6 → p4)) ∨ ((p4 ∧ p7) → (p2 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_18 : (((True → False) → (p6 → p4)) ∨ ((p4 ∧ p7) → (p2 ∧ p2))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p6 : Prop)
theorem file95_101965 : (((((True → False) → False) ∨ ((True ∨ True) ∧ (p1 ∧ p6))) → False) → False) := by
  intro assump_31
  have assump_45 : (((True → False) → False) ∨ ((True ∨ True) ∧ (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_35
    have assump_46 : True := by
      apply True.intro
    let assump_38 := assump_35 assump_46
    apply False.elim assump_38
  let assump_34 := assump_31 assump_45
  apply False.elim assump_34


variable (p3 p7 p1 p0 p2 p4 p6 : Prop)
theorem file95_102443 : (((((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) → False) → ((((p7 ∨ p3) ∧ (p2 → False)) ∨ ((True → False) ∧ (p6 ∨ p1))) → (((False ∨ p0) → False) ∧ ((p3 → False) ∨ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply False.elim assump_4
  case inr assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          have assump_178 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
            apply Or.inl
            intro assump_23
            cases assump_23
            case intro assump_24 assump_25 =>
              apply Or.inl
              exact assump_24
          let assump_22 := assump_1 assump_178
          apply False.elim assump_22
        case inr assump_15 =>
          have assump_179 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
            apply Or.inl
            intro assump_40
            cases assump_40
            case intro assump_41 assump_42 =>
              apply Or.inl
              exact assump_41
          let assump_39 := assump_1 assump_179
          apply False.elim assump_39
    case inr assump_11 =>
      cases assump_11
      case intro assump_50 assump_51 =>
        cases assump_51
        case inl assump_54 =>
          have assump_180 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
            apply Or.inl
            intro assump_61
            cases assump_61
            case intro assump_62 assump_63 =>
              apply Or.inl
              exact assump_62
          let assump_60 := assump_1 assump_180
          apply False.elim assump_60
        case inr assump_55 =>
          have assump_181 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
            apply Or.inl
            intro assump_76
            cases assump_76
            case intro assump_77 assump_78 =>
              apply Or.inl
              exact assump_77
          let assump_75 := assump_1 assump_181
          apply False.elim assump_75
  cases assump_2
  case inl assump_86 =>
    cases assump_86
    case intro assump_88 assump_89 =>
      cases assump_88
      case inl assump_90 =>
        apply Or.inl
        intro assump_98
        have assump_182 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
          apply Or.inl
          intro assump_103
          cases assump_103
          case intro assump_104 assump_105 =>
            apply Or.inl
            exact assump_104
        let assump_102 := assump_1 assump_182
        apply False.elim assump_102
      case inr assump_91 =>
        apply Or.inl
        intro assump_119
        have assump_183 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
          apply Or.inl
          intro assump_124
          cases assump_124
          case intro assump_125 assump_126 =>
            apply Or.inl
            exact assump_125
        let assump_123 := assump_1 assump_183
        apply False.elim assump_123
  case inr assump_87 =>
    cases assump_87
    case intro assump_134 assump_135 =>
      cases assump_135
      case inl assump_138 =>
        apply Or.inl
        intro assump_144
        have assump_184 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
          apply Or.inl
          intro assump_149
          cases assump_149
          case intro assump_150 assump_151 =>
            apply Or.inl
            exact assump_150
        let assump_148 := assump_1 assump_184
        apply False.elim assump_148
      case inr assump_139 =>
        apply Or.inl
        intro assump_163
        have assump_185 : (((p0 ∧ p6) → (p0 ∨ p3)) ∨ ((p4 ∧ p3) → (True → False))) := by
          apply Or.inl
          intro assump_168
          cases assump_168
          case intro assump_169 assump_170 =>
            apply Or.inl
            exact assump_169
        let assump_167 := assump_1 assump_185
        apply False.elim assump_167


variable (p1 p4 p6 p5 p3 : Prop)
theorem file95_106576 : ((((((p3 ∨ p5) ∧ (False → False)) ∧ ((True ∨ p1) → (p6 ∧ False))) ∨ (((p1 ∧ p1) ∨ (False → p6)) ∨ ((True → False) → (False ∧ p3)))) → ((((True → False) → (True ∨ p6)) → False) ∧ (((p1 → False) → False) ∧ ((p4 ∧ p4) → False)))) → False) := by
  intro assump_1
  have assump_16 : ((((p3 ∨ p5) ∧ (False → False)) ∧ ((True ∨ p1) → (p6 ∧ False))) ∨ (((p1 ∧ p1) ∨ (False → p6)) ∨ ((True → False) → (False ∧ p3)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_16
  let assump_8 := And.left assump_4
  have assump_17 : ((True → False) → (True ∨ p6)) := by
    intro assump_10
    apply Or.inl
    apply True.intro
  let assump_9 := assump_8 assump_17
  apply False.elim assump_9


variable (p0 p7 p5 p3 : Prop)
theorem file95_107396 : ((((((p7 → False) ∨ (p3 ∧ False)) ∧ ((False ∧ p5) ∧ (p0 ∨ p3))) → False) → False) → False) := by
  intro assump_9
  have assump_35 : ((((p7 → False) ∨ (p3 ∧ False)) ∧ ((False ∧ p5) ∧ (p0 ∨ p3))) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_15
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
      case inr assump_17 =>
        cases assump_17
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
  let assump_12 := assump_9 assump_35
  apply False.elim assump_12


variable (p2 p7 p5 p6 p4 p0 p3 : Prop)
theorem file95_108170 : ((((((False ∧ p7) ∨ (p4 ∧ p2)) → ((True → p2) → False)) → (((p6 ∧ p0) ∨ (p5 ∨ p4)) ∨ ((p2 → False) → (p3 → p3)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∧ p7) ∨ (p4 ∧ p2)) → ((True → p2) → False)) → (((p6 ∧ p0) ∨ (p5 ∨ p4)) ∨ ((p2 → False) → (p3 → p3)))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    intro assump_9
    exact assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p1 p6 p2 p3 : Prop)
theorem file95_108677 : ((((((True → p7) ∨ (p3 ∧ p1)) → False) → (((p3 ∧ False) ∧ (p6 ∨ p2)) → ((p1 → True) ∧ (p1 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True → p7) ∨ (p3 ∧ p1)) → False) → (((p3 ∧ False) ∧ (p6 ∨ p2)) → ((p1 → True) ∧ (p1 ∨ p3)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    apply True.intro
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p3 p1 p5 p2 p0 : Prop)
theorem file95_109313 : (((((p3 ∧ p1) → False) ∨ ((p4 → False) → False)) ∨ (((p3 → False) → False) ∨ ((p3 → False) ∨ (p3 → p5)))) → ((((p1 → p2) → (True ∨ p0)) ∧ ((True → False) → (True ∨ p5))) ∧ (((p1 ∧ False) → (p1 → False)) ∨ ((p5 ∧ p2) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
  case inr assump_6 =>
    cases assump_6
    case inl assump_13 =>
      apply Or.inl
      apply True.intro
    case inr assump_14 =>
      cases assump_14
      case inl assump_17 =>
        apply Or.inl
        apply True.intro
      case inr assump_18 =>
        apply Or.inl
        apply True.intro
  intro assump_23
  cases assump_1
  case inl assump_26 =>
    cases assump_26
    case inl assump_28 =>
      apply Or.inl
      apply True.intro
    case inr assump_29 =>
      apply Or.inl
      apply True.intro
  case inr assump_27 =>
    cases assump_27
    case inl assump_34 =>
      apply Or.inl
      apply True.intro
    case inr assump_35 =>
      cases assump_35
      case inl assump_38 =>
        apply Or.inl
        apply True.intro
      case inr assump_39 =>
        apply Or.inl
        apply True.intro
  cases assump_1
  case inl assump_44 =>
    cases assump_44
    case inl assump_46 =>
      apply Or.inl
      intro assump_50
      intro assump_51
      cases assump_50
      case intro assump_54 assump_55 =>
        apply False.elim assump_55
    case inr assump_47 =>
      apply Or.inl
      intro assump_62
      intro assump_63
      cases assump_62
      case intro assump_66 assump_67 =>
        apply False.elim assump_67
  case inr assump_45 =>
    cases assump_45
    case inl assump_72 =>
      apply Or.inl
      intro assump_76
      intro assump_77
      cases assump_76
      case intro assump_80 assump_81 =>
        apply False.elim assump_81
    case inr assump_73 =>
      cases assump_73
      case inl assump_86 =>
        apply Or.inl
        intro assump_90
        intro assump_91
        cases assump_90
        case intro assump_94 assump_95 =>
          apply False.elim assump_95
      case inr assump_87 =>
        apply Or.inl
        intro assump_102
        intro assump_103
        cases assump_102
        case intro assump_106 assump_107 =>
          apply False.elim assump_107


variable (p7 p0 p6 p5 : Prop)
theorem file95_111810 : ((((((p7 ∧ p6) → (p5 ∨ p6)) → False) → (((False ∧ p0) ∨ (p6 ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p7 ∧ p6) → (p5 ∨ p6)) → False) → (((False ∧ p0) ∨ (p6 ∨ p0)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_8 =>
      cases assump_8
      case inl assump_13 =>
        have assump_49 : ((p7 ∧ p6) → (p5 ∨ p6)) := by
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            apply Or.inr
            exact assump_22
        let assump_19 := assump_5 assump_49
        apply False.elim assump_19
      case inr assump_14 =>
        have assump_50 : ((p7 ∧ p6) → (p5 ∨ p6)) := by
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            apply Or.inr
            exact assump_37
        let assump_34 := assump_5 assump_50
        apply False.elim assump_34
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p3 p6 p1 p7 p0 p2 p4 : Prop)
theorem file95_113000 : ((((((p2 → p3) ∧ (p6 → False)) ∨ ((p6 ∨ p3) ∧ (p6 → p7))) ∨ (((True ∧ p1) → False) ∨ ((p7 → False) → (False → False)))) ∧ ((((False ∧ p7) → False) → False) ∧ (((p4 ∧ p4) → False) ∧ ((p0 → False) ∧ (p7 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                have assump_162 : ((False ∧ p7) → False) := by
                  intro assump_32
                  cases assump_32
                  case intro assump_33 assump_34 =>
                    apply False.elim assump_33
                let assump_31 := assump_14 assump_162
                apply False.elim assump_31
      case inr assump_7 =>
        cases assump_7
        case intro assump_40 assump_41 =>
          cases assump_40
          case inl assump_42 =>
            cases assump_3
            case intro assump_48 assump_49 =>
              cases assump_49
              case intro assump_52 assump_53 =>
                cases assump_53
                case intro assump_56 assump_57 =>
                  have assump_163 : ((False ∧ p7) → False) := by
                    intro assump_66
                    cases assump_66
                    case intro assump_67 assump_68 =>
                      apply False.elim assump_67
                  let assump_65 := assump_48 assump_163
                  apply False.elim assump_65
          case inr assump_43 =>
            cases assump_3
            case intro assump_78 assump_79 =>
              cases assump_79
              case intro assump_82 assump_83 =>
                cases assump_83
                case intro assump_86 assump_87 =>
                  have assump_164 : ((False ∧ p7) → False) := by
                    intro assump_96
                    cases assump_96
                    case intro assump_97 assump_98 =>
                      apply False.elim assump_97
                  let assump_95 := assump_78 assump_164
                  apply False.elim assump_95
    case inr assump_5 =>
      cases assump_5
      case inl assump_104 =>
        cases assump_3
        case intro assump_108 assump_109 =>
          cases assump_109
          case intro assump_112 assump_113 =>
            cases assump_113
            case intro assump_116 assump_117 =>
              have assump_165 : ((False ∧ p7) → False) := by
                intro assump_126
                cases assump_126
                case intro assump_127 assump_128 =>
                  apply False.elim assump_127
              let assump_125 := assump_108 assump_165
              apply False.elim assump_125
      case inr assump_105 =>
        cases assump_3
        case intro assump_136 assump_137 =>
          cases assump_137
          case intro assump_140 assump_141 =>
            cases assump_141
            case intro assump_144 assump_145 =>
              have assump_166 : ((False ∧ p7) → False) := by
                intro assump_154
                cases assump_154
                case intro assump_155 assump_156 =>
                  apply False.elim assump_155
              let assump_153 := assump_136 assump_166
              apply False.elim assump_153


variable (p7 p5 p4 p6 : Prop)
theorem file95_116564 : (((((p6 → p7) → (p5 → False)) → ((p6 ∨ p4) → (p6 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_20 : (((p6 → p7) → (p5 → False)) → ((p6 ∨ p4) → (p6 ∨ p4))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      exact assump_7
    case inr assump_8 =>
      apply Or.inr
      exact assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p7 p4 p0 p6 p2 : Prop)
theorem file95_117054 : (((((False → True) ∧ (p4 → True)) ∨ ((False ∨ p3) ∨ (p0 → p4))) ∧ (((True ∧ False) ∧ (p2 ∨ p7)) ∧ ((p0 ∨ p7) → (p3 ∨ p2)))) → ((((p4 ∨ False) ∧ (p4 → p4)) ∧ ((p6 → True) → (True → p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_16
              case intro assump_25 assump_26 =>
                cases assump_25
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case intro assump_29 assump_30 =>
                    apply False.elim assump_30
          case inr assump_18 =>
            cases assump_18
            case inl assump_35 =>
              cases assump_35
              case inl assump_37 =>
                apply False.elim assump_37
              case inr assump_38 =>
                cases assump_16
                case intro assump_43 assump_44 =>
                  cases assump_43
                  case intro assump_45 assump_46 =>
                    cases assump_45
                    case intro assump_47 assump_48 =>
                      apply False.elim assump_48
            case inr assump_36 =>
              cases assump_16
              case intro assump_55 assump_56 =>
                cases assump_55
                case intro assump_57 assump_58 =>
                  cases assump_57
                  case intro assump_59 assump_60 =>
                    apply False.elim assump_60
      case inr assump_8 =>
        apply False.elim assump_8


variable (p0 p4 p2 p1 p6 p5 p3 : Prop)
theorem file95_118931 : (((((p2 → p2) → False) ∧ ((p3 → False) ∨ (p1 ∧ p6))) → (((p5 → False) ∧ (p6 → False)) → ((p1 → p0) → (p5 → False)))) ∨ ((((p4 ∨ p0) ∨ (p3 ∨ p4)) → ((False → False) ∨ (p2 ∨ p4))) ∧ (((p3 ∨ p1) → False) → ((True ∨ p3) ∧ (True ∨ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_1
    case intro assump_15 assump_16 =>
      cases assump_16
      case inl assump_19 =>
        have assump_46 : (p2 → p2) := by
          intro assump_25
          exact assump_25
        let assump_24 := assump_15 assump_46
        apply False.elim assump_24
      case inr assump_20 =>
        cases assump_20
        case intro assump_31 assump_32 =>
          have assump_47 : (p2 → p2) := by
            intro assump_40
            exact assump_40
          let assump_39 := assump_15 assump_47
          apply False.elim assump_39


variable (p2 p3 p7 p1 p0 p5 : Prop)
theorem file95_119925 : (((((False → False) ∨ (p5 → False)) ∨ ((True → False) ∨ (p2 ∨ p5))) ∨ (((False ∧ p0) ∧ (False ∨ p3)) ∧ ((p1 → False) → (p7 → False)))) ∨ ((((p2 ∧ p0) → False) ∧ ((False → p3) ∨ (p2 ∨ False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p6 p2 : Prop)
theorem file95_120286 : ((((((p6 → p6) ∨ (p2 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p6 → p6) ∨ (p2 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p6 → p6) ∨ (p2 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


