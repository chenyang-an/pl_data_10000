variable (p7 p5 p6 p0 p2 p4 p1 : Prop)
theorem file19_47 : (((((p1 ∧ p6) ∨ (True ∧ p5)) → ((p5 → False) → False)) → (((False → p5) ∨ (p7 → p5)) → False)) → ((((p5 → p6) ∨ (p4 → p0)) → ((p7 → False) → (p4 ∨ True))) ∨ (((p6 → False) → (p2 ∧ p5)) → ((p6 ∧ p6) → (p4 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    apply Or.inr
    apply True.intro
  case inr assump_9 =>
    apply Or.inr
    apply True.intro


variable (p7 p3 p1 p6 p5 p4 p2 p0 : Prop)
theorem file19_541 : (((((p1 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p0) → (p6 → p5))) → False) → ((((p3 ∨ p2) ∧ (p6 → False)) ∨ ((p6 ∨ p5) → (p7 → False))) ∧ (((p6 → p3) → False) ∧ ((p4 → False) → (p3 ∨ p4))))) := by
  intro assump_1
  apply And.intro
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_192 : (((p1 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p0) → (p6 → p5))) := by
      intro assump_15
      intro assump_16
      intro assump_17
      cases assump_16
      case inl assump_20 =>
        cases assump_15
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            have assump_193 : p1 := by
              exact assump_26
            let assump_34 := assump_25 assump_193
            apply False.elim assump_34
      case inr assump_21 =>
        cases assump_15
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            have assump_194 : p1 := by
              exact assump_42
            let assump_50 := assump_41 assump_194
            apply False.elim assump_50
    let assump_14 := assump_1 assump_192
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_195 : (((p1 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p0) → (p6 → p5))) := by
      intro assump_62
      intro assump_63
      intro assump_64
      cases assump_63
      case inl assump_67 =>
        cases assump_62
        case intro assump_71 assump_72 =>
          cases assump_71
          case intro assump_73 assump_74 =>
            exact assump_9
      case inr assump_68 =>
        cases assump_62
        case intro assump_83 assump_84 =>
          cases assump_83
          case intro assump_85 assump_86 =>
            exact assump_9
    let assump_61 := assump_1 assump_195
    apply False.elim assump_61
  apply And.intro
  intro assump_96
  have assump_196 : (((p1 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p0) → (p6 → p5))) := by
    intro assump_102
    intro assump_103
    intro assump_104
    cases assump_103
    case inl assump_107 =>
      cases assump_102
      case intro assump_111 assump_112 =>
        cases assump_111
        case intro assump_113 assump_114 =>
          have assump_197 : p1 := by
            exact assump_113
          let assump_121 := assump_112 assump_197
          apply False.elim assump_121
    case inr assump_108 =>
      cases assump_102
      case intro assump_127 assump_128 =>
        cases assump_127
        case intro assump_129 assump_130 =>
          have assump_198 : p1 := by
            exact assump_129
          let assump_137 := assump_128 assump_198
          apply False.elim assump_137
  let assump_101 := assump_1 assump_196
  apply False.elim assump_101
  intro assump_144
  have assump_199 : (((p1 ∧ p4) ∧ (p1 → False)) → ((p0 ∨ p0) → (p6 → p5))) := by
    intro assump_150
    intro assump_151
    intro assump_152
    cases assump_151
    case inl assump_155 =>
      cases assump_150
      case intro assump_159 assump_160 =>
        cases assump_159
        case intro assump_161 assump_162 =>
          have assump_200 : p1 := by
            exact assump_161
          let assump_169 := assump_160 assump_200
          apply False.elim assump_169
    case inr assump_156 =>
      cases assump_150
      case intro assump_175 assump_176 =>
        cases assump_175
        case intro assump_177 assump_178 =>
          have assump_201 : p1 := by
            exact assump_177
          let assump_185 := assump_176 assump_201
          apply False.elim assump_185
  let assump_149 := assump_1 assump_199
  apply False.elim assump_149


variable (p6 p3 p0 p4 p7 p5 : Prop)
theorem file19_4233 : (((((p3 ∧ p6) ∧ (p4 ∧ p7)) ∧ ((p7 → False) → (True ∧ p0))) → False) → ((((p0 → False) ∧ (p7 → False)) ∧ ((p3 ∧ p0) ∨ (True ∧ p5))) → (((p3 → p3) ∧ (p5 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            have assump_52 : p0 := by
              exact assump_21
            let assump_32 := assump_12 assump_52
            apply False.elim assump_32
        case inr assump_19 =>
          cases assump_19
          case intro assump_36 assump_37 =>
            have assump_53 : p5 := by
              exact assump_37
            let assump_48 := assump_5 assump_53
            apply False.elim assump_48


variable (p7 p3 p6 p5 p1 p0 p2 : Prop)
theorem file19_5230 : ((((((p2 ∨ p3) ∨ (p7 ∧ True)) ∨ ((p6 → False) → (p2 → p7))) ∧ (((p3 ∨ p5) → (p7 → p6)) → ((p1 ∨ p0) ∨ (True ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p2 ∨ p3) ∨ (p7 ∧ True)) ∨ ((p6 → False) → (p2 → p7))) ∧ (((p3 ∨ p5) → (p7 → p6)) → ((p1 ∨ p0) ∨ (True ∨ p1)))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    intro assump_6
    have assump_27 : ((((p2 ∨ p3) ∨ (p7 ∧ True)) ∨ ((p6 → False) → (p2 → p7))) ∧ (((p3 ∨ p5) → (p7 → p6)) → ((p1 ∨ p0) ∨ (True ∨ p1)))) := by
      apply And.intro
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_6
      intro assump_14
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_13 := assump_1 assump_27
    apply False.elim assump_13
    intro assump_20
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p3 p5 p6 : Prop)
theorem file19_6193 : (((((p3 → p0) → False) ∧ ((False → p6) → False)) ∧ (((p5 ∧ False) → (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : ((p5 ∧ False) → (p0 → False)) := by
        intro assump_13
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      let assump_12 := assump_3 assump_26
      apply False.elim assump_12


variable (p5 p1 p2 p0 : Prop)
theorem file19_6762 : ((((((True ∨ p1) → False) → False) ∨ (((p0 ∧ p0) → (p5 ∨ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p1) → False) → False) ∨ (((p0 ∧ p0) → (p5 ∨ p2)) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p1) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p0 p6 p4 p1 p7 p2 : Prop)
theorem file19_7284 : (((((p4 ∨ p6) ∨ (p7 ∨ True)) ∨ ((p7 → False) → (p2 ∨ p7))) ∨ (((p6 → False) → False) → False)) ∨ ((((p4 ∧ True) ∧ (p1 ∨ True)) ∨ ((p7 ∧ p0) ∨ (p3 → False))) → (((p6 ∨ p4) ∨ (p6 ∨ False)) → ((True → p7) ∨ (p3 → p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p6 p4 p2 p0 p7 p1 : Prop)
theorem file19_7662 : (((((p1 ∧ p0) ∨ (p7 ∨ p2)) ∨ ((p1 ∧ p6) ∨ (p4 ∧ p4))) → (((p6 ∧ p7) → (p0 ∧ p7)) ∧ ((p1 → False) ∧ (False ∨ p7)))) → ((((False ∧ p4) → (p7 ∨ p6)) ∧ ((False ∧ False) ∧ (p1 ∨ p1))) → (((p0 ∨ True) ∧ (p1 → p2)) ∨ ((p0 ∨ False) ∧ (False ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p6 p2 p4 p5 p1 p3 : Prop)
theorem file19_8208 : (((((True ∨ p2) → (True ∨ p3)) ∧ ((p1 ∨ p2) ∨ (p1 → p2))) → False) → ((((p4 ∧ p4) → False) → False) ∧ (((p2 → False) ∧ (p2 → p3)) ∨ ((p6 ∨ p5) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_65 : (((True ∨ p2) → (True ∨ p3)) ∧ ((p1 ∨ p2) ∨ (p1 → p2))) := by
    apply And.intro
    intro assump_8
    cases assump_8
    case inl assump_9 =>
      apply Or.inl
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply True.intro
    apply Or.inr
    intro assump_15
    have assump_66 : (((True ∨ p2) → (True ∨ p3)) ∧ ((p1 ∨ p2) ∨ (p1 → p2))) := by
      apply And.intro
      intro assump_20
      cases assump_20
      case inl assump_21 =>
        apply Or.inl
        apply True.intro
      case inr assump_22 =>
        apply Or.inl
        apply True.intro
      apply Or.inl
      apply Or.inl
      exact assump_15
    let assump_19 := assump_1 assump_66
    apply False.elim assump_19
  let assump_7 := assump_1 assump_65
  apply False.elim assump_7
  apply Or.inl
  apply And.intro
  intro assump_35
  have assump_67 : (((True ∨ p2) → (True ∨ p3)) ∧ ((p1 ∨ p2) ∨ (p1 → p2))) := by
    apply And.intro
    intro assump_40
    cases assump_40
    case inl assump_41 =>
      apply Or.inl
      apply True.intro
    case inr assump_42 =>
      apply Or.inl
      apply True.intro
    apply Or.inl
    apply Or.inr
    exact assump_35
  let assump_39 := assump_1 assump_67
  apply False.elim assump_39
  intro assump_50
  have assump_68 : (((True ∨ p2) → (True ∨ p3)) ∧ ((p1 ∨ p2) ∨ (p1 → p2))) := by
    apply And.intro
    intro assump_55
    cases assump_55
    case inl assump_56 =>
      apply Or.inl
      apply True.intro
    case inr assump_57 =>
      apply Or.inl
      apply True.intro
    apply Or.inl
    apply Or.inr
    exact assump_50
  let assump_54 := assump_1 assump_68
  apply False.elim assump_54


variable (p6 p3 p0 : Prop)
theorem file19_10141 : ((((((p6 → False) ∧ (p3 ∨ False)) ∧ ((p0 → True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 → False) ∧ (p3 ∨ False)) ∧ ((p0 → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_29 : (p0 → True) := by
            intro assump_19
            apply True.intro
          let assump_18 := assump_7 assump_29
          apply False.elim assump_18
        case inr assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p2 p7 p1 p0 p3 p4 : Prop)
theorem file19_10907 : ((((((p0 → p6) → (p2 ∧ p0)) ∨ ((p3 ∧ False) ∨ (p1 ∧ p0))) → (((True ∨ p4) ∨ (p7 ∨ p2)) ∨ ((p0 → p6) ∨ (p0 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p0 → p6) → (p2 ∧ p0)) ∨ ((p3 ∧ False) ∨ (p1 ∧ p0))) → (((True ∨ p4) ∨ (p7 ∨ p2)) ∨ ((p0 → p6) ∨ (p0 ∧ p0)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
      case inr assump_11 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p1 p3 p6 p4 p7 p0 p2 : Prop)
theorem file19_11839 : (((((p2 → False) ∧ (p4 → False)) ∧ ((p2 → False) → (p2 → p6))) ∧ (((False → False) ∧ (False ∧ p0)) ∨ ((p1 ∨ p1) ∧ (p2 ∨ p7)))) → ((((p3 ∧ False) ∧ (p0 ∧ p2)) ∧ ((p2 ∨ p0) → False)) → (((p3 ∧ p2) ∨ (p6 → p6)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  case inr assump_5 =>
    cases assump_2
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply False.elim assump_29


variable (p3 p5 p7 : Prop)
theorem file19_12742 : (((((p3 ∨ p5) ∨ (p7 → False)) → ((False → p5) ∧ (False → p7))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p3 ∨ p5) ∨ (p7 → False)) → ((False → p5) ∧ (False → p7))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p5 p1 p7 p3 p0 p4 : Prop)
theorem file19_13197 : ((((((p1 → False) ∨ (p7 → p2)) ∨ ((p3 ∨ p4) → False)) ∧ (((False ∨ p0) → False) ∧ ((p1 ∨ True) ∧ (p4 → p4)))) ∧ ((((p5 ∨ p2) → False) → False) ∧ (((p1 ∨ p1) ∨ (p3 → False)) ∧ ((p1 ∨ p1) ∧ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            cases assump_13
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_3
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_30
                      case inl assump_32 =>
                        cases assump_29
                        case intro assump_36 assump_37 =>
                          cases assump_36
                          case inl assump_38 =>
                            have assump_520 : p1 := by
                              exact assump_38
                            let assump_44 := assump_37 assump_520
                            apply False.elim assump_44
                          case inr assump_39 =>
                            have assump_521 : p1 := by
                              exact assump_39
                            let assump_52 := assump_37 assump_521
                            apply False.elim assump_52
                      case inr assump_33 =>
                        cases assump_29
                        case intro assump_58 assump_59 =>
                          cases assump_58
                          case inl assump_60 =>
                            have assump_522 : p1 := by
                              exact assump_60
                            let assump_66 := assump_59 assump_522
                            apply False.elim assump_66
                          case inr assump_61 =>
                            have assump_523 : p1 := by
                              exact assump_61
                            let assump_74 := assump_59 assump_523
                            apply False.elim assump_74
                    case inr assump_31 =>
                      cases assump_29
                      case intro assump_80 assump_81 =>
                        cases assump_80
                        case inl assump_82 =>
                          have assump_524 : p1 := by
                            exact assump_82
                          let assump_88 := assump_81 assump_524
                          apply False.elim assump_88
                        case inr assump_83 =>
                          have assump_525 : p1 := by
                            exact assump_83
                          let assump_96 := assump_81 assump_525
                          apply False.elim assump_96
              case inr assump_19 =>
                cases assump_3
                case intro assump_104 assump_105 =>
                  cases assump_105
                  case intro assump_108 assump_109 =>
                    cases assump_108
                    case inl assump_110 =>
                      cases assump_110
                      case inl assump_112 =>
                        cases assump_109
                        case intro assump_116 assump_117 =>
                          cases assump_116
                          case inl assump_118 =>
                            have assump_526 : p1 := by
                              exact assump_118
                            let assump_124 := assump_117 assump_526
                            apply False.elim assump_124
                          case inr assump_119 =>
                            have assump_527 : p1 := by
                              exact assump_119
                            let assump_132 := assump_117 assump_527
                            apply False.elim assump_132
                      case inr assump_113 =>
                        cases assump_109
                        case intro assump_138 assump_139 =>
                          cases assump_138
                          case inl assump_140 =>
                            have assump_528 : p1 := by
                              exact assump_140
                            let assump_146 := assump_139 assump_528
                            apply False.elim assump_146
                          case inr assump_141 =>
                            have assump_529 : p1 := by
                              exact assump_141
                            let assump_154 := assump_139 assump_529
                            apply False.elim assump_154
                    case inr assump_111 =>
                      cases assump_109
                      case intro assump_160 assump_161 =>
                        cases assump_160
                        case inl assump_162 =>
                          have assump_530 : p1 := by
                            exact assump_162
                          let assump_168 := assump_161 assump_530
                          apply False.elim assump_168
                        case inr assump_163 =>
                          have assump_531 : p1 := by
                            exact assump_163
                          let assump_176 := assump_161 assump_531
                          apply False.elim assump_176
        case inr assump_9 =>
          cases assump_5
          case intro assump_182 assump_183 =>
            cases assump_183
            case intro assump_186 assump_187 =>
              cases assump_186
              case inl assump_188 =>
                cases assump_3
                case intro assump_194 assump_195 =>
                  cases assump_195
                  case intro assump_198 assump_199 =>
                    cases assump_198
                    case inl assump_200 =>
                      cases assump_200
                      case inl assump_202 =>
                        cases assump_199
                        case intro assump_206 assump_207 =>
                          cases assump_206
                          case inl assump_208 =>
                            have assump_532 : p1 := by
                              exact assump_208
                            let assump_214 := assump_207 assump_532
                            apply False.elim assump_214
                          case inr assump_209 =>
                            have assump_533 : p1 := by
                              exact assump_209
                            let assump_222 := assump_207 assump_533
                            apply False.elim assump_222
                      case inr assump_203 =>
                        cases assump_199
                        case intro assump_228 assump_229 =>
                          cases assump_228
                          case inl assump_230 =>
                            have assump_534 : p1 := by
                              exact assump_230
                            let assump_236 := assump_229 assump_534
                            apply False.elim assump_236
                          case inr assump_231 =>
                            have assump_535 : p1 := by
                              exact assump_231
                            let assump_244 := assump_229 assump_535
                            apply False.elim assump_244
                    case inr assump_201 =>
                      cases assump_199
                      case intro assump_250 assump_251 =>
                        cases assump_250
                        case inl assump_252 =>
                          have assump_536 : p1 := by
                            exact assump_252
                          let assump_258 := assump_251 assump_536
                          apply False.elim assump_258
                        case inr assump_253 =>
                          have assump_537 : p1 := by
                            exact assump_253
                          let assump_266 := assump_251 assump_537
                          apply False.elim assump_266
              case inr assump_189 =>
                cases assump_3
                case intro assump_274 assump_275 =>
                  cases assump_275
                  case intro assump_278 assump_279 =>
                    cases assump_278
                    case inl assump_280 =>
                      cases assump_280
                      case inl assump_282 =>
                        cases assump_279
                        case intro assump_286 assump_287 =>
                          cases assump_286
                          case inl assump_288 =>
                            have assump_538 : p1 := by
                              exact assump_288
                            let assump_294 := assump_287 assump_538
                            apply False.elim assump_294
                          case inr assump_289 =>
                            have assump_539 : p1 := by
                              exact assump_289
                            let assump_302 := assump_287 assump_539
                            apply False.elim assump_302
                      case inr assump_283 =>
                        cases assump_279
                        case intro assump_308 assump_309 =>
                          cases assump_308
                          case inl assump_310 =>
                            have assump_540 : p1 := by
                              exact assump_310
                            let assump_316 := assump_309 assump_540
                            apply False.elim assump_316
                          case inr assump_311 =>
                            have assump_541 : p1 := by
                              exact assump_311
                            let assump_324 := assump_309 assump_541
                            apply False.elim assump_324
                    case inr assump_281 =>
                      cases assump_279
                      case intro assump_330 assump_331 =>
                        cases assump_330
                        case inl assump_332 =>
                          have assump_542 : p1 := by
                            exact assump_332
                          let assump_338 := assump_331 assump_542
                          apply False.elim assump_338
                        case inr assump_333 =>
                          have assump_543 : p1 := by
                            exact assump_333
                          let assump_346 := assump_331 assump_543
                          apply False.elim assump_346
      case inr assump_7 =>
        cases assump_5
        case intro assump_352 assump_353 =>
          cases assump_353
          case intro assump_356 assump_357 =>
            cases assump_356
            case inl assump_358 =>
              cases assump_3
              case intro assump_364 assump_365 =>
                cases assump_365
                case intro assump_368 assump_369 =>
                  cases assump_368
                  case inl assump_370 =>
                    cases assump_370
                    case inl assump_372 =>
                      cases assump_369
                      case intro assump_376 assump_377 =>
                        cases assump_376
                        case inl assump_378 =>
                          have assump_544 : p1 := by
                            exact assump_378
                          let assump_384 := assump_377 assump_544
                          apply False.elim assump_384
                        case inr assump_379 =>
                          have assump_545 : p1 := by
                            exact assump_379
                          let assump_392 := assump_377 assump_545
                          apply False.elim assump_392
                    case inr assump_373 =>
                      cases assump_369
                      case intro assump_398 assump_399 =>
                        cases assump_398
                        case inl assump_400 =>
                          have assump_546 : p1 := by
                            exact assump_400
                          let assump_406 := assump_399 assump_546
                          apply False.elim assump_406
                        case inr assump_401 =>
                          have assump_547 : p1 := by
                            exact assump_401
                          let assump_414 := assump_399 assump_547
                          apply False.elim assump_414
                  case inr assump_371 =>
                    cases assump_369
                    case intro assump_420 assump_421 =>
                      cases assump_420
                      case inl assump_422 =>
                        have assump_548 : p1 := by
                          exact assump_422
                        let assump_428 := assump_421 assump_548
                        apply False.elim assump_428
                      case inr assump_423 =>
                        have assump_549 : p1 := by
                          exact assump_423
                        let assump_436 := assump_421 assump_549
                        apply False.elim assump_436
            case inr assump_359 =>
              cases assump_3
              case intro assump_444 assump_445 =>
                cases assump_445
                case intro assump_448 assump_449 =>
                  cases assump_448
                  case inl assump_450 =>
                    cases assump_450
                    case inl assump_452 =>
                      cases assump_449
                      case intro assump_456 assump_457 =>
                        cases assump_456
                        case inl assump_458 =>
                          have assump_550 : p1 := by
                            exact assump_458
                          let assump_464 := assump_457 assump_550
                          apply False.elim assump_464
                        case inr assump_459 =>
                          have assump_551 : p1 := by
                            exact assump_459
                          let assump_472 := assump_457 assump_551
                          apply False.elim assump_472
                    case inr assump_453 =>
                      cases assump_449
                      case intro assump_478 assump_479 =>
                        cases assump_478
                        case inl assump_480 =>
                          have assump_552 : p1 := by
                            exact assump_480
                          let assump_486 := assump_479 assump_552
                          apply False.elim assump_486
                        case inr assump_481 =>
                          have assump_553 : p1 := by
                            exact assump_481
                          let assump_494 := assump_479 assump_553
                          apply False.elim assump_494
                  case inr assump_451 =>
                    cases assump_449
                    case intro assump_500 assump_501 =>
                      cases assump_500
                      case inl assump_502 =>
                        have assump_554 : p1 := by
                          exact assump_502
                        let assump_508 := assump_501 assump_554
                        apply False.elim assump_508
                      case inr assump_503 =>
                        have assump_555 : p1 := by
                          exact assump_503
                        let assump_516 := assump_501 assump_555
                        apply False.elim assump_516


variable (p2 p7 : Prop)
theorem file19_29112 : (((((False ∧ p7) → False) → False) ∧ (((False ∨ p2) → (False → False)) → ((True → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : ((False ∨ p2) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_18
    have assump_19 : (True → True) := by
      intro assump_14
      apply True.intro
    let assump_13 := assump_8 assump_19
    apply False.elim assump_13


variable (p1 p7 p4 p0 p2 p6 p5 p3 : Prop)
theorem file19_29692 : (((((p3 → False) → (False ∨ p3)) → False) → (((p3 → False) ∨ (p6 ∨ p2)) ∨ ((p1 ∨ p2) → (p5 ∨ p4)))) ∨ ((((p2 → p1) ∧ (p2 → False)) ∧ ((p0 ∨ True) → (p6 ∨ p7))) → (((False ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_9
  apply Or.inl
  apply Or.inl
  intro assump_12
  have assump_23 : ((p3 → False) → (False ∨ p3)) := by
    intro assump_17
    apply Or.inr
    exact assump_12
  let assump_16 := assump_9 assump_23
  apply False.elim assump_16


variable (p7 p6 p2 p5 p1 p0 : Prop)
theorem file19_30214 : ((((((True → False) ∨ (p5 → False)) ∨ ((True → False) → False)) → False) ∧ ((((True → True) ∧ (False → False)) → ((p7 ∨ p1) → (p2 → False))) ∧ (((p0 ∨ True) → False) ∧ ((True ∧ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_21 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_17 := assump_10 assump_21
        apply False.elim assump_17


variable (p2 p0 p6 p1 p3 p5 : Prop)
theorem file19_30839 : (((((False ∧ p3) → (p1 → False)) → False) ∧ (((p0 ∨ p6) → (p5 → p2)) ∧ ((p2 ∧ p0) ∧ (p2 ∧ p5)))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          cases assump_25
          case intro assump_32 assump_33 =>
            have assump_57 : ((False ∧ p3) → (p1 → False)) := by
              intro assump_46
              intro assump_47
              cases assump_46
              case intro assump_50 assump_51 =>
                apply False.elim assump_50
            let assump_45 := assump_16 assump_57
            apply False.elim assump_45


variable (p5 p2 p1 p0 p4 p7 : Prop)
theorem file19_31673 : ((((((True ∧ p0) → False) → False) → (((p0 → p5) → False) ∨ ((p7 → p2) → False))) ∧ ((((p2 ∧ False) → False) → False) ∧ (((True ∧ True) ∧ (p5 ∨ p5)) → ((p4 ∨ p1) ∨ (p0 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_24 : ((p2 ∧ False) → False) := by
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      let assump_13 := assump_6 assump_24
      apply False.elim assump_13


variable (p6 p3 p5 p1 p4 p7 p2 : Prop)
theorem file19_32306 : (((((p7 ∧ p5) ∧ (p6 → False)) ∧ ((False ∧ p3) ∧ (p7 → False))) → False) ∨ ((((False ∧ p7) ∧ (p7 ∨ p3)) ∨ ((p1 ∨ p4) ∨ (p3 → p2))) ∨ (((p2 → False) → False) ∧ ((p7 → True) → False)))) := by
  apply Or.inl
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
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p2 p1 p6 p3 p7 p0 p5 : Prop)
theorem file19_32929 : (((((p0 → False) ∧ (p3 ∧ False)) ∧ ((p5 → False) → False)) → (((False → False) → (p6 ∧ p7)) → False)) → ((((p3 → p2) ∧ (True → p1)) → False) → (((p3 → False) → (p3 → False)) ∨ ((True → p5) ∨ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  have assump_17 : p3 := by
    exact assump_8
  let assump_13 := assump_7 assump_17
  apply False.elim assump_13


variable (p0 p5 p3 p1 p6 p4 : Prop)
theorem file19_33400 : ((((((p3 ∧ p1) → (p3 ∨ p4)) → False) → False) → ((((p5 ∧ p0) → (p4 ∨ p6)) → ((p5 → False) → (True → True))) → False)) → False) := by
  intro assump_1
  have assump_26 : ((((p3 ∧ p1) → (p3 ∨ p4)) → False) → False) := by
    intro assump_5
    have assump_27 : ((p3 ∧ p1) → (p3 ∨ p4)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        exact assump_10
    let assump_8 := assump_5 assump_27
    apply False.elim assump_8
  let assump_4 := assump_1 assump_26
  have assump_28 : (((p5 ∧ p0) → (p4 ∨ p6)) → ((p5 → False) → (True → True))) := by
    intro assump_20
    intro assump_21
    intro assump_22
    apply True.intro
  let assump_19 := assump_4 assump_28
  apply False.elim assump_19


variable (p5 p6 p7 p4 p3 p1 : Prop)
theorem file19_34214 : ((((((p5 → p5) → (p1 → True)) ∨ ((False → p5) → (True → False))) ∨ (((p5 → False) ∨ (p4 ∨ p4)) ∨ ((p6 → False) ∨ (p3 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_10 : ((((p5 → p5) → (p1 → True)) ∨ ((False → p5) → (True → False))) ∨ (((p5 → False) ∨ (p4 ∨ p4)) ∨ ((p6 → False) ∨ (p3 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p0 p1 p3 p5 p7 p6 : Prop)
theorem file19_34748 : ((((((p7 → p1) ∧ (True ∧ p1)) → ((p3 ∨ p5) → False)) ∨ (((False ∨ p1) ∨ (p0 → p3)) ∧ ((p7 ∧ p6) → False))) ∧ ((((True ∧ False) ∧ (p5 → p1)) ∧ ((p3 → False) → (p7 → False))) ∧ (((p6 → p5) ∨ (p6 → False)) → ((p7 → False) ∨ (p5 → False))))) → False) := by
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
              apply False.elim assump_15
    case inr assump_5 =>
      cases assump_5
      case intro assump_20 assump_21 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_22
          case inl assump_24 =>
            apply False.elim assump_24
          case inr assump_25 =>
            cases assump_3
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_34
                case intro assump_36 assump_37 =>
                  cases assump_36
                  case intro assump_38 assump_39 =>
                    apply False.elim assump_39
        case inr assump_23 =>
          cases assump_3
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_52
                case intro assump_54 assump_55 =>
                  apply False.elim assump_55


variable (p2 p7 p4 p3 p1 p0 : Prop)
theorem file19_36495 : (((((p0 → False) ∧ (p7 → False)) → False) → (((True → False) → (True ∨ p7)) ∨ ((p3 → False) → False))) ∨ ((((False → p7) ∨ (p3 → False)) ∨ ((True → p2) → False)) ∨ (((p1 ∨ p4) → False) → False))) := by
  apply Or.inl
  intro assump_7
  apply Or.inl
  intro assump_10
  apply Or.inl
  apply True.intro


variable (p3 p4 p5 p2 p6 p0 p7 : Prop)
theorem file19_36859 : (((((p2 ∧ p7) ∧ (False → False)) → ((p2 → False) → (p3 → p3))) ∧ (((False ∧ p0) → (p6 → False)) → False)) → ((((p2 ∨ p5) → False) → False) → (((p4 ∧ p6) → False) ∨ ((True ∧ p5) ∧ (p2 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      have assump_32 : ((False ∧ p0) → (p6 → False)) := by
        intro assump_21
        intro assump_22
        cases assump_21
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      let assump_20 := assump_6 assump_32
      apply False.elim assump_20


variable (p4 p7 p1 p0 p5 p6 p3 : Prop)
theorem file19_37589 : (((((p3 ∨ p0) ∨ (p0 ∨ p5)) ∧ ((p7 ∨ False) → False)) ∧ (((p4 ∧ p4) ∨ (p4 → False)) → False)) → ((((p6 ∧ p1) ∨ (p3 → p1)) → False) ∨ (((p0 → False) ∨ (p3 ∨ p6)) ∨ ((False ∧ True) → (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          intro assump_16
          cases assump_16
          case inl assump_17 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              have assump_202 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inr
                intro assump_28
                have assump_203 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_28
                  exact assump_28
                let assump_34 := assump_3 assump_203
                apply False.elim assump_34
              let assump_27 := assump_3 assump_202
              apply False.elim assump_27
          case inr assump_18 =>
            have assump_204 : ((p4 ∧ p4) ∨ (p4 → False)) := by
              apply Or.inr
              intro assump_46
              have assump_205 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inl
                apply And.intro
                exact assump_46
                exact assump_46
              let assump_52 := assump_3 assump_205
              apply False.elim assump_52
            let assump_45 := assump_3 assump_204
            apply False.elim assump_45
        case inr assump_9 =>
          apply Or.inl
          intro assump_65
          cases assump_65
          case inl assump_66 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              have assump_206 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inr
                intro assump_77
                have assump_207 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_77
                  exact assump_77
                let assump_83 := assump_3 assump_207
                apply False.elim assump_83
              let assump_76 := assump_3 assump_206
              apply False.elim assump_76
          case inr assump_67 =>
            have assump_208 : ((p4 ∧ p4) ∨ (p4 → False)) := by
              apply Or.inr
              intro assump_94
              have assump_209 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inl
                apply And.intro
                exact assump_94
                exact assump_94
              let assump_99 := assump_3 assump_209
              apply False.elim assump_99
            let assump_93 := assump_3 assump_208
            apply False.elim assump_93
      case inr assump_7 =>
        cases assump_7
        case inl assump_106 =>
          apply Or.inl
          intro assump_114
          cases assump_114
          case inl assump_115 =>
            cases assump_115
            case intro assump_117 assump_118 =>
              have assump_210 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inr
                intro assump_126
                have assump_211 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_126
                  exact assump_126
                let assump_132 := assump_3 assump_211
                apply False.elim assump_132
              let assump_125 := assump_3 assump_210
              apply False.elim assump_125
          case inr assump_116 =>
            have assump_212 : ((p4 ∧ p4) ∨ (p4 → False)) := by
              apply Or.inr
              intro assump_143
              have assump_213 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inl
                apply And.intro
                exact assump_143
                exact assump_143
              let assump_148 := assump_3 assump_213
              apply False.elim assump_148
            let assump_142 := assump_3 assump_212
            apply False.elim assump_142
        case inr assump_107 =>
          apply Or.inl
          intro assump_161
          cases assump_161
          case inl assump_162 =>
            cases assump_162
            case intro assump_164 assump_165 =>
              have assump_214 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inr
                intro assump_173
                have assump_215 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_173
                  exact assump_173
                let assump_179 := assump_3 assump_215
                apply False.elim assump_179
              let assump_172 := assump_3 assump_214
              apply False.elim assump_172
          case inr assump_163 =>
            have assump_216 : ((p4 ∧ p4) ∨ (p4 → False)) := by
              apply Or.inr
              intro assump_190
              have assump_217 : ((p4 ∧ p4) ∨ (p4 → False)) := by
                apply Or.inl
                apply And.intro
                exact assump_190
                exact assump_190
              let assump_195 := assump_3 assump_217
              apply False.elim assump_195
            let assump_189 := assump_3 assump_216
            apply False.elim assump_189


variable (p4 p2 p5 p7 p0 p1 p3 : Prop)
theorem file19_43129 : (((((p1 ∨ p7) → False) → ((p1 → p5) ∧ (False → p4))) → (((p7 ∧ p2) ∨ (False → False)) → ((p1 → p0) ∧ (p5 ∨ p2)))) → ((((p3 → False) → False) → ((p3 → True) ∨ (p3 → False))) ∨ (((p3 → False) → False) → False))) := by
  intro assump_6
  apply Or.inl
  intro assump_9
  apply Or.inl
  intro assump_12
  apply True.intro


variable (p5 p6 p2 p4 p0 p3 p7 : Prop)
theorem file19_43509 : ((((((p0 → False) ∧ (False ∧ p2)) ∨ ((p3 ∧ p3) ∨ (p0 → False))) → (((p2 → p7) ∨ (p0 ∨ p7)) → False)) ∧ ((((p6 → False) ∨ (p2 → False)) ∧ ((p4 → p2) ∨ (True → False))) ∧ (((p5 ∨ True) ∨ (p7 → p0)) → False))) → False) := by
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
          case inl assump_14 =>
            have assump_52 : ((p5 ∨ True) ∨ (p7 → p0)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_20 := assump_7 assump_52
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_53 : ((p5 ∨ True) ∨ (p7 → p0)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_28 := assump_7 assump_53
            apply False.elim assump_28
        case inr assump_11 =>
          cases assump_9
          case inl assump_34 =>
            have assump_54 : ((p5 ∨ True) ∨ (p7 → p0)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_40 := assump_7 assump_54
            apply False.elim assump_40
          case inr assump_35 =>
            have assump_55 : ((p5 ∨ True) ∨ (p7 → p0)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_48 := assump_7 assump_55
            apply False.elim assump_48


variable (p7 p3 p0 : Prop)
theorem file19_45157 : ((((((False ∨ p3) ∧ (p0 ∧ False)) ∧ ((p7 → p0) ∨ (p7 ∨ p7))) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False ∨ p3) ∧ (p0 ∧ False)) ∧ ((p7 → p0) ∨ (p7 ∨ p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p6 p2 p5 p0 p1 p7 p4 : Prop)
theorem file19_45853 : (((((p0 → False) ∨ (p4 ∨ p3)) ∨ ((p1 → False) ∧ (p5 ∨ p4))) → (((p4 → False) ∧ (True → False)) → ((p6 → p7) ∧ (p7 → False)))) ∨ ((((p2 ∨ p4) → (False ∨ p2)) ∧ ((p4 → False) ∨ (p4 ∨ p6))) ∨ (((False → p6) ∨ (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_20
  intro assump_21
  apply And.intro
  intro assump_22
  cases assump_21
  case intro assump_25 assump_26 =>
    cases assump_20
    case inl assump_31 =>
      cases assump_31
      case inl assump_33 =>
        have assump_138 : True := by
          apply True.intro
        let assump_38 := assump_26 assump_138
        apply False.elim assump_38
      case inr assump_34 =>
        cases assump_34
        case inl assump_42 =>
          have assump_139 : True := by
            apply True.intro
          let assump_47 := assump_26 assump_139
          apply False.elim assump_47
        case inr assump_43 =>
          have assump_140 : True := by
            apply True.intro
          let assump_54 := assump_26 assump_140
          apply False.elim assump_54
    case inr assump_32 =>
      cases assump_32
      case intro assump_58 assump_59 =>
        cases assump_59
        case inl assump_62 =>
          have assump_141 : True := by
            apply True.intro
          let assump_68 := assump_26 assump_141
          apply False.elim assump_68
        case inr assump_63 =>
          have assump_142 : True := by
            apply True.intro
          let assump_76 := assump_26 assump_142
          apply False.elim assump_76
  intro assump_80
  cases assump_21
  case intro assump_83 assump_84 =>
    cases assump_20
    case inl assump_89 =>
      cases assump_89
      case inl assump_91 =>
        have assump_143 : True := by
          apply True.intro
        let assump_96 := assump_84 assump_143
        apply False.elim assump_96
      case inr assump_92 =>
        cases assump_92
        case inl assump_100 =>
          have assump_144 : True := by
            apply True.intro
          let assump_105 := assump_84 assump_144
          apply False.elim assump_105
        case inr assump_101 =>
          have assump_145 : True := by
            apply True.intro
          let assump_112 := assump_84 assump_145
          apply False.elim assump_112
    case inr assump_90 =>
      cases assump_90
      case intro assump_116 assump_117 =>
        cases assump_117
        case inl assump_120 =>
          have assump_146 : True := by
            apply True.intro
          let assump_126 := assump_84 assump_146
          apply False.elim assump_126
        case inr assump_121 =>
          have assump_147 : True := by
            apply True.intro
          let assump_134 := assump_84 assump_147
          apply False.elim assump_134


variable (p2 p0 p5 p7 p4 p3 p6 : Prop)
theorem file19_48655 : (((((p3 → p3) → (False → p6)) ∧ ((False → p0) → False)) → False) ∨ ((((p2 → p0) → (p2 ∨ p7)) → False) ∧ (((p5 ∧ p5) ∨ (p2 → False)) ∧ ((p4 ∧ p7) → (True → p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → p0) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p3 p0 p2 : Prop)
theorem file19_49123 : (((((p3 → False) ∨ (p3 ∧ False)) → ((False ∧ False) → False)) → False) → ((((p0 → False) ∨ (p4 ∧ p2)) ∧ ((p2 → False) ∨ (p0 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        have assump_75 : (((p3 → False) ∨ (p3 ∧ False)) → ((False ∧ False) → False)) := by
          intro assump_16
          intro assump_17
          cases assump_17
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
        let assump_15 := assump_1 assump_75
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_76 : (((p3 → False) ∨ (p3 ∧ False)) → ((False ∧ False) → False)) := by
          intro assump_30
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
        let assump_29 := assump_1 assump_76
        apply False.elim assump_29
    case inr assump_6 =>
      cases assump_6
      case intro assump_39 assump_40 =>
        cases assump_4
        case inl assump_45 =>
          have assump_77 : (((p3 → False) ∨ (p3 ∧ False)) → ((False ∧ False) → False)) := by
            intro assump_52
            intro assump_53
            cases assump_53
            case intro assump_54 assump_55 =>
              apply False.elim assump_54
          let assump_51 := assump_1 assump_77
          apply False.elim assump_51
        case inr assump_46 =>
          have assump_78 : (((p3 → False) ∨ (p3 ∧ False)) → ((False ∧ False) → False)) := by
            intro assump_66
            intro assump_67
            cases assump_67
            case intro assump_68 assump_69 =>
              apply False.elim assump_68
          let assump_65 := assump_1 assump_78
          apply False.elim assump_65


variable (p1 p2 p4 p5 p3 p6 : Prop)
theorem file19_51064 : (((((p5 ∧ p3) ∧ (False ∨ False)) → False) ∨ (((p4 → p1) ∧ (False ∨ p2)) ∨ ((True ∧ p4) ∧ (p6 ∨ p1)))) ∨ ((((p5 ∧ p3) → (True → False)) ∨ ((p4 ∧ p3) → (p2 ∧ p3))) ∧ (((p4 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply False.elim assump_11


variable (p0 p7 p3 p4 p1 p2 p6 : Prop)
theorem file19_51632 : ((((((p4 ∧ p7) ∨ (p2 ∨ p7)) → ((p0 → False) ∨ (p3 ∧ False))) ∨ (((p6 → p4) → (False → False)) → False)) ∧ ((((p2 ∧ p1) ∨ (p3 ∨ p6)) → False) ∧ (((p7 ∨ p1) ∨ (p2 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_32 : ((p7 ∨ p1) ∨ (p2 → True)) := by
          apply Or.inr
          intro assump_15
          apply True.intro
        let assump_14 := assump_9 assump_32
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_21 assump_22 =>
        have assump_33 : ((p7 ∨ p1) ∨ (p2 → True)) := by
          apply Or.inr
          intro assump_28
          apply True.intro
        let assump_27 := assump_22 assump_33
        apply False.elim assump_27


variable (p7 p6 p0 p5 p3 : Prop)
theorem file19_52567 : (((((p0 ∨ p7) → (p7 ∧ True)) → False) ∧ (((p7 ∨ p5) ∨ (False → p6)) → False)) → ((((p0 → False) → False) → ((p3 ∧ p7) → False)) → False)) := by
  intro assump_37
  intro assump_38
  cases assump_37
  case intro assump_41 assump_42 =>
    have assump_54 : ((p7 ∨ p5) ∨ (False → p6)) := by
      apply Or.inr
      intro assump_48
      apply False.elim assump_48
    let assump_47 := assump_42 assump_54
    apply False.elim assump_47


variable (p5 p1 p0 p2 p3 : Prop)
theorem file19_53058 : ((((((True ∧ p3) → (p3 → p2)) → ((p5 ∨ True) → False)) ∧ (((p0 → False) → (p5 ∨ p3)) → ((p0 → False) ∨ (p2 ∨ p2)))) ∧ ((((True → False) → False) ∨ ((p5 ∨ p0) → (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((True → False) → False) ∨ ((p5 ∨ p0) → (p1 → False))) := by
        apply Or.inl
        intro assump_13
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p6 p1 p2 p0 : Prop)
theorem file19_53783 : ((((((p1 ∨ False) → False) → ((p2 → p6) → (p2 → True))) → False) ∧ ((((True → False) → (p6 → False)) ∨ ((p6 → False) → (p0 → p1))) → (((False ∧ False) ∨ (p1 ∧ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : (((p1 ∨ False) → False) → ((p2 → p6) → (p2 → True))) := by
      intro assump_21
      intro assump_22
      intro assump_23
      apply True.intro
    let assump_20 := assump_2 assump_27
    apply False.elim assump_20


variable (p4 p5 p0 p7 p3 p1 p2 p6 : Prop)
theorem file19_54347 : (((((False ∨ p3) ∨ (p6 → False)) ∨ ((False ∨ p3) → (p5 ∨ p4))) → (((p7 → p6) ∧ (p7 ∧ True)) → ((False → False) ∨ (True → p4)))) ∨ ((((p0 ∧ p3) → False) ∧ ((p3 → False) ∧ (p6 → p4))) ∨ (((p1 ∨ True) ∧ (p4 ∨ p6)) ∨ ((p1 ∨ p1) ∨ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply Or.inl
            intro assump_23
            apply False.elim assump_23
        case inr assump_16 =>
          apply Or.inl
          intro assump_28
          apply False.elim assump_28
      case inr assump_14 =>
        apply Or.inl
        intro assump_33
        apply False.elim assump_33


variable (p2 : Prop)
theorem file19_55344 : ((((((p2 → p2) ∨ (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → p2) ∨ (False → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p2 → p2) ∨ (False → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p2 p1 p7 p0 p6 p4 p5 : Prop)
theorem file19_55849 : (((((False ∧ p2) → False) ∨ ((p7 → False) ∧ (p6 ∨ p4))) ∨ (((p2 → False) ∧ (p6 ∨ p4)) ∨ ((p2 → p3) ∧ (p2 ∧ p0)))) ∨ ((((p6 → False) → False) ∧ ((p3 → False) ∧ (p3 ∨ p3))) ∧ (((p6 ∧ p1) ∨ (p5 ∨ False)) → ((p7 ∧ p1) ∧ (True → p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p3 p0 p5 p6 p7 p4 : Prop)
theorem file19_56290 : (((((True ∨ False) ∨ (False → False)) ∨ ((p3 → p4) ∧ (p6 ∧ p0))) → False) → ((((p7 ∧ True) ∧ (False → False)) → ((p5 → False) ∧ (p3 → False))) → (((p0 ∧ True) → False) ∧ ((p5 ∨ p6) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_41 : (((True ∨ False) ∨ (False → False)) ∨ ((p3 → p4) ∧ (p6 ∧ p0))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_14 := assump_1 assump_41
    apply False.elim assump_14
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    have assump_42 : (((True ∨ False) ∨ (False → False)) ∨ ((p3 → p4) ∧ (p6 ∧ p0))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_27 := assump_1 assump_42
    apply False.elim assump_27
  case inr assump_20 =>
    have assump_43 : (((True ∨ False) ∨ (False → False)) ∨ ((p3 → p4) ∧ (p6 ∧ p0))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_37 := assump_1 assump_43
    apply False.elim assump_37


variable (p3 p5 p2 p4 p7 p6 p1 : Prop)
theorem file19_57479 : (((((p7 → False) → (p1 → p2)) → False) → (((p3 → p4) ∨ (p3 → False)) → ((p4 → False) → False))) → ((((p3 → False) ∧ (p1 → True)) ∧ ((p2 ∨ p2) → (p1 ∨ p1))) → (((p6 ∧ False) ∧ (p5 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p3 p0 p1 p5 p4 : Prop)
theorem file19_57931 : (((((False ∧ p1) → (p0 → p3)) → False) → False) ∨ ((((p4 ∨ p5) ∨ (True → False)) ∧ ((True ∧ False) → (p5 → False))) → (((p3 → True) → (p4 → True)) ∨ ((p0 ∧ p0) ∨ (p5 ∧ p3))))) := by
  apply Or.inl
  intro assump_14
  have assump_29 : ((False ∧ p1) → (p0 → p3)) := by
    intro assump_18
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      apply False.elim assump_22
  let assump_17 := assump_14 assump_29
  apply False.elim assump_17


variable (p4 p0 p7 p2 p3 p1 : Prop)
theorem file19_58457 : ((((((p2 → False) → (True ∨ p3)) ∧ ((True ∧ False) → (p0 ∨ p1))) ∨ (((p0 ∧ p4) → (True → p3)) ∨ ((p0 → False) ∧ (p7 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → False) → (True ∨ p3)) ∧ ((True ∧ False) → (p0 ∨ p1))) ∨ (((p0 ∧ p4) → (True → p3)) ∨ ((p0 → False) ∧ (p7 ∧ p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply Or.inl
    apply True.intro
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p5 p3 p4 p1 p7 : Prop)
theorem file19_59098 : (((((False → p1) → False) ∧ ((True → False) ∨ (p5 → p4))) ∧ (((p3 → False) ∨ (p1 → p3)) ∧ ((p5 ∧ p2) ∧ (p5 → p7)))) → False) := by
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
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_116 : True := by
                  apply True.intro
                let assump_33 := assump_8 assump_116
                apply False.elim assump_33
          case inr assump_15 =>
            cases assump_13
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                have assump_117 : True := by
                  apply True.intro
                let assump_54 := assump_8 assump_117
                apply False.elim assump_54
      case inr assump_9 =>
        cases assump_3
        case intro assump_60 assump_61 =>
          cases assump_60
          case inl assump_62 =>
            cases assump_61
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                have assump_118 : (False → p1) := by
                  intro assump_84
                  apply False.elim assump_84
                let assump_83 := assump_4 assump_118
                apply False.elim assump_83
          case inr assump_63 =>
            cases assump_61
            case intro assump_92 assump_93 =>
              cases assump_92
              case intro assump_94 assump_95 =>
                have assump_119 : (False → p1) := by
                  intro assump_110
                  apply False.elim assump_110
                let assump_109 := assump_4 assump_119
                apply False.elim assump_109


variable (p2 p3 p4 p0 : Prop)
theorem file19_61211 : (((((p2 → True) ∨ (p0 → False)) ∨ ((p4 ∧ p4) ∨ (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p2 → True) ∨ (p0 → False)) ∨ ((p4 ∧ p4) ∨ (p3 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p6 p5 p2 p4 p0 p1 : Prop)
theorem file19_61596 : ((((((False → False) ∨ (p1 ∧ p5)) → False) → (((p6 ∨ False) ∧ (p2 ∨ True)) → False)) ∧ ((((p2 ∧ p4) → False) ∧ ((p0 → p0) → False)) ∧ (((p2 ∧ True) ∧ (p6 ∧ False)) ∨ ((False → False) → (p2 ∧ p0))))) → False) := by
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
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
        case inr assump_15 =>
          have assump_46 : (p0 → p0) := by
            intro assump_40
            exact assump_40
          let assump_39 := assump_9 assump_46
          apply False.elim assump_39


variable (p3 p1 p4 p0 p2 p5 p6 p7 : Prop)
theorem file19_62588 : ((((((p7 ∨ p1) → False) ∨ ((p2 → False) → False)) ∧ (((p7 ∧ False) ∨ (p4 → p5)) ∨ ((p3 ∧ p0) ∨ (p3 ∨ p0)))) ∧ ((((p5 ∨ False) → (True ∧ p5)) → ((p5 → p1) ∧ (True ∨ p6))) ∧ (((False ∧ False) → (p7 ∨ False)) → False))) → False) := by
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
          case inl assump_12 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              apply False.elim assump_15
          case inr assump_13 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              have assump_184 : ((False ∧ False) → (p7 ∨ False)) := by
                intro assump_29
                cases assump_29
                case intro assump_30 assump_31 =>
                  apply False.elim assump_30
              let assump_28 := assump_23 assump_184
              apply False.elim assump_28
        case inr assump_11 =>
          cases assump_11
          case inl assump_37 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              cases assump_3
              case intro assump_45 assump_46 =>
                have assump_185 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_52
                  cases assump_52
                  case intro assump_53 assump_54 =>
                    apply False.elim assump_53
                let assump_51 := assump_46 assump_185
                apply False.elim assump_51
          case inr assump_38 =>
            cases assump_38
            case inl assump_60 =>
              cases assump_3
              case intro assump_64 assump_65 =>
                have assump_186 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_71
                  cases assump_71
                  case intro assump_72 assump_73 =>
                    apply False.elim assump_72
                let assump_70 := assump_65 assump_186
                apply False.elim assump_70
            case inr assump_61 =>
              cases assump_3
              case intro assump_81 assump_82 =>
                have assump_187 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_88
                  cases assump_88
                  case intro assump_89 assump_90 =>
                    apply False.elim assump_89
                let assump_87 := assump_82 assump_187
                apply False.elim assump_87
      case inr assump_7 =>
        cases assump_5
        case inl assump_98 =>
          cases assump_98
          case inl assump_100 =>
            cases assump_100
            case intro assump_102 assump_103 =>
              apply False.elim assump_103
          case inr assump_101 =>
            cases assump_3
            case intro assump_110 assump_111 =>
              have assump_188 : ((False ∧ False) → (p7 ∨ False)) := by
                intro assump_117
                cases assump_117
                case intro assump_118 assump_119 =>
                  apply False.elim assump_118
              let assump_116 := assump_111 assump_188
              apply False.elim assump_116
        case inr assump_99 =>
          cases assump_99
          case inl assump_125 =>
            cases assump_125
            case intro assump_127 assump_128 =>
              cases assump_3
              case intro assump_133 assump_134 =>
                have assump_189 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_140
                  cases assump_140
                  case intro assump_141 assump_142 =>
                    apply False.elim assump_141
                let assump_139 := assump_134 assump_189
                apply False.elim assump_139
          case inr assump_126 =>
            cases assump_126
            case inl assump_148 =>
              cases assump_3
              case intro assump_152 assump_153 =>
                have assump_190 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_159
                  cases assump_159
                  case intro assump_160 assump_161 =>
                    apply False.elim assump_160
                let assump_158 := assump_153 assump_190
                apply False.elim assump_158
            case inr assump_149 =>
              cases assump_3
              case intro assump_169 assump_170 =>
                have assump_191 : ((False ∧ False) → (p7 ∨ False)) := by
                  intro assump_176
                  cases assump_176
                  case intro assump_177 assump_178 =>
                    apply False.elim assump_177
                let assump_175 := assump_170 assump_191
                apply False.elim assump_175


variable (p6 p4 p5 p0 : Prop)
theorem file19_67498 : ((((((False → False) ∨ (p5 → False)) ∧ ((p0 ∧ p5) ∨ (p6 ∨ p0))) → (((p0 → p5) ∧ (p0 ∧ p4)) → ((p4 ∨ p4) ∨ (p6 → False)))) → False) → False) := by
  intro assump_16
  have assump_71 : ((((False → False) ∨ (p5 → False)) ∧ ((p0 ∧ p5) ∨ (p6 ∨ p0))) → (((p0 → p5) ∧ (p0 ∧ p4)) → ((p4 ∨ p4) ∨ (p6 → False)))) := by
    intro assump_20
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        cases assump_20
        case intro assump_32 assump_33 =>
          cases assump_32
          case inl assump_34 =>
            cases assump_33
            case inl assump_38 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
            case inr assump_39 =>
              cases assump_39
              case inl assump_46 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
              case inr assump_47 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
          case inr assump_35 =>
            cases assump_33
            case inl assump_54 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
            case inr assump_55 =>
              cases assump_55
              case inl assump_62 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
              case inr assump_63 =>
                apply Or.inl
                apply Or.inl
                exact assump_27
  let assump_19 := assump_16 assump_71
  apply False.elim assump_19


variable (p7 p6 p2 p3 : Prop)
theorem file19_69337 : (((((p2 ∨ p6) → False) → False) ∧ (((True ∨ p7) ∨ (p3 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((True ∨ p7) ∨ (p3 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p5 p6 p4 p0 : Prop)
theorem file19_69737 : ((((((p5 ∨ p4) ∨ (True ∨ p0)) → False) → (((p5 → False) ∨ (p6 → p3)) → ((p4 → False) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p5 ∨ p4) ∨ (True ∨ p0)) → False) → (((p5 → False) ∨ (p6 → p3)) → ((p4 → False) → (p6 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case inl assump_13 =>
      have assump_35 : ((p5 ∨ p4) ∨ (True ∨ p0)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_19 := assump_5 assump_35
      apply False.elim assump_19
    case inr assump_14 =>
      have assump_36 : ((p5 ∨ p4) ∨ (True ∨ p0)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_27 := assump_5 assump_36
      apply False.elim assump_27
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p4 p6 p2 p5 p3 p0 : Prop)
theorem file19_70673 : (((((True → False) → False) ∧ ((p5 → p0) ∧ (p0 ∧ p5))) → False) → ((((p6 → True) → (False → False)) ∨ ((p3 → False) → (p3 ∧ p4))) ∨ (((True ∨ False) → False) ∨ ((p6 → p4) ∨ (p2 → p2))))) := by
  intro assump_33
  apply Or.inl
  apply Or.inl
  intro assump_36
  intro assump_37
  apply False.elim assump_37


variable (p4 p6 p7 : Prop)
theorem file19_71030 : ((((((False ∨ p6) → False) ∧ ((p7 → False) ∧ (p4 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False ∨ p6) → False) ∧ ((p7 → False) ∧ (p4 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p4 p3 p6 : Prop)
theorem file19_71589 : ((((((p6 → p3) → (True → p4)) ∧ ((False → False) → False)) → (((p0 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p6 → p3) → (True → p4)) ∧ ((False → False) → False)) → (((p0 → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_26 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_10 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p4 p0 p3 p5 p2 p7 : Prop)
theorem file19_72245 : (((((p1 ∧ p3) ∧ (p1 ∧ p7)) → ((p5 ∨ p1) ∨ (p4 → False))) → False) → ((((p1 ∨ p0) ∧ (True → False)) ∧ ((p2 ∧ False) ∧ (p7 ∧ True))) ∨ (((True → False) ∨ (p2 → p3)) → ((p2 → p2) ∧ (True ∧ False))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  apply And.intro
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    exact assump_5
  case inr assump_9 =>
    exact assump_5
  apply And.intro
  apply True.intro
  cases assump_4
  case inl assump_14 =>
    have assump_44 : True := by
      apply True.intro
    let assump_18 := assump_14 assump_44
    apply False.elim assump_18
  case inr assump_15 =>
    have assump_45 : (((p1 ∧ p3) ∧ (p1 ∧ p7)) → ((p5 ∨ p1) ∨ (p4 → False))) := by
      intro assump_26
      cases assump_26
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_28
          case intro assump_35 assump_36 =>
            apply Or.inl
            apply Or.inr
            exact assump_35
    let assump_25 := assump_1 assump_45
    apply False.elim assump_25


variable (p5 p3 p2 p7 p4 p6 p0 : Prop)
theorem file19_73376 : ((((((p2 → False) ∨ (p4 ∧ p0)) ∨ ((p4 ∧ False) ∧ (p5 ∨ p4))) → (((p4 → False) ∨ (p6 → p6)) ∨ ((p7 → True) → (p6 → True)))) ∧ ((((p7 ∧ p4) ∨ (p6 → p4)) → False) ∧ (((True → False) ∧ (p5 → p7)) ∧ ((True → False) ∨ (p7 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case inl assump_18 =>
            have assump_44 : True := by
              apply True.intro
            let assump_22 := assump_18 assump_44
            apply False.elim assump_22
          case inr assump_19 =>
            cases assump_19
            case inl assump_26 =>
              have assump_45 : True := by
                apply True.intro
              let assump_32 := assump_12 assump_45
              apply False.elim assump_32
            case inr assump_27 =>
              have assump_46 : True := by
                apply True.intro
              let assump_40 := assump_12 assump_46
              apply False.elim assump_40


variable (p6 p5 p4 p1 p3 p2 p0 : Prop)
theorem file19_74609 : ((((((p4 ∨ p6) → (p0 → p0)) ∨ ((p3 ∨ p2) → False)) ∨ (((True ∨ p1) → False) ∧ ((p2 ∨ p3) ∧ (p3 → p5)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 ∨ p6) → (p0 → p0)) ∨ ((p3 ∨ p2) → False)) ∨ (((True ∨ p1) → False) ∧ ((p2 ∨ p3) ∧ (p3 → p5)))) := by
    apply Or.inl
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


variable (p3 p5 p1 p7 p6 p0 p4 p2 : Prop)
theorem file19_75196 : (((((p6 ∧ p1) ∧ (True ∨ p4)) ∧ ((p1 ∧ p1) ∨ (p0 ∨ False))) ∧ (((p5 ∨ False) → (p2 ∧ True)) ∨ ((True → p0) → False))) ∨ ((((p5 ∧ p2) ∧ (p1 ∧ p4)) → ((p0 → False) ∧ (p3 ∧ False))) → (((p0 → p7) ∧ (p3 → p2)) → ((p5 ∨ False) ∨ (p5 → True))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    intro assump_11
    apply True.intro


variable (p1 p7 p0 p3 p4 p6 p5 p2 : Prop)
theorem file19_75665 : ((((((False ∨ p4) → (p0 → p4)) ∨ ((p3 → p7) → (p0 → False))) ∨ (((p0 ∨ p4) → False) ∨ ((False ∧ False) → (p5 → False)))) ∧ ((((p7 ∨ p1) ∧ (p6 ∧ p5)) → ((p0 ∧ p2) ∨ (p2 ∨ True))) ∧ (((p2 → False) → (p1 → p1)) → ((False ∧ True) ∧ (p5 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_90 : ((p2 → False) → (p1 → p1)) := by
            intro assump_17
            intro assump_18
            exact assump_18
          let assump_16 := assump_11 assump_90
          let assump_23 := And.left assump_16
          let assump_24 := And.left assump_23
          apply False.elim assump_24
      case inr assump_7 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          have assump_91 : ((p2 → False) → (p1 → p1)) := by
            intro assump_37
            intro assump_38
            exact assump_38
          let assump_36 := assump_31 assump_91
          let assump_43 := And.left assump_36
          let assump_44 := And.left assump_43
          apply False.elim assump_44
    case inr assump_5 =>
      cases assump_5
      case inl assump_48 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          have assump_92 : ((p2 → False) → (p1 → p1)) := by
            intro assump_59
            intro assump_60
            exact assump_60
          let assump_58 := assump_53 assump_92
          let assump_65 := And.left assump_58
          let assump_66 := And.left assump_65
          apply False.elim assump_66
      case inr assump_49 =>
        cases assump_3
        case intro assump_72 assump_73 =>
          have assump_93 : ((p2 → False) → (p1 → p1)) := by
            intro assump_79
            intro assump_80
            exact assump_80
          let assump_78 := assump_73 assump_93
          let assump_85 := And.left assump_78
          let assump_86 := And.left assump_85
          apply False.elim assump_86


variable (p3 p1 p7 p5 p4 p0 p2 : Prop)
theorem file19_77814 : ((((((p5 ∧ False) → (p5 → p7)) ∨ ((p0 → p7) → False)) → False) ∧ ((((p3 ∧ True) → False) ∨ ((p1 ∧ p0) → (p2 ∧ p2))) ∨ (((p0 ∨ False) → (p3 ∧ False)) ∧ ((p4 → p4) ∨ (p3 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_86 : (((p5 ∧ False) → (p5 → p7)) ∨ ((p0 → p7) → False)) := by
          apply Or.inl
          intro assump_14
          intro assump_15
          cases assump_14
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
        let assump_13 := assump_2 assump_86
        apply False.elim assump_13
      case inr assump_9 =>
        have assump_87 : (((p5 ∧ False) → (p5 → p7)) ∨ ((p0 → p7) → False)) := by
          apply Or.inl
          intro assump_31
          intro assump_32
          cases assump_31
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
        let assump_30 := assump_2 assump_87
        apply False.elim assump_30
    case inr assump_7 =>
      cases assump_7
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          have assump_88 : (((p5 ∧ False) → (p5 → p7)) ∨ ((p0 → p7) → False)) := by
            apply Or.inl
            intro assump_55
            intro assump_56
            cases assump_55
            case intro assump_59 assump_60 =>
              apply False.elim assump_60
          let assump_54 := assump_2 assump_88
          apply False.elim assump_54
        case inr assump_49 =>
          have assump_89 : (((p5 ∧ False) → (p5 → p7)) ∨ ((p0 → p7) → False)) := by
            apply Or.inl
            intro assump_73
            intro assump_74
            cases assump_73
            case intro assump_77 assump_78 =>
              apply False.elim assump_78
          let assump_72 := assump_2 assump_89
          apply False.elim assump_72


variable (p7 p3 p5 p2 p6 : Prop)
theorem file19_79837 : (((((True ∨ p6) ∧ (False → False)) ∧ ((True ∨ p3) ∨ (p5 ∧ p2))) → (((p2 → False) → (p7 ∨ True)) → False)) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p6) ∧ (False → False)) ∧ ((True ∨ p3) ∨ (p5 ∧ p2))) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_5
    apply False.elim assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_15
  have assump_16 : ((p2 → False) → (p7 ∨ True)) := by
    intro assump_9
    apply Or.inr
    apply True.intro
  let assump_8 := assump_4 assump_16
  apply False.elim assump_8


variable (p6 p1 p5 p2 p4 p7 p3 : Prop)
theorem file19_80520 : (((((False → p4) → False) ∧ ((p7 ∨ p5) ∧ (p2 → True))) → (((p7 ∧ p2) ∧ (p7 → False)) ∨ ((p3 ∧ True) ∨ (p6 → p1)))) ∧ ((((False ∧ p2) ∨ (True → False)) ∧ ((p5 → p2) ∧ (False ∧ p7))) → False)) := by
  apply And.intro
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        apply Or.inr
        apply Or.inr
        intro assump_22
        have assump_71 : (False → p4) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_10 assump_71
        apply False.elim assump_28
      case inr assump_17 =>
        apply Or.inr
        apply Or.inr
        intro assump_39
        have assump_72 : (False → p4) := by
          intro assump_46
          apply False.elim assump_46
        let assump_45 := assump_10 assump_72
        apply False.elim assump_45
  intro assump_52
  cases assump_52
  case intro assump_53 assump_54 =>
    cases assump_53
    case inl assump_55 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        apply False.elim assump_57
    case inr assump_56 =>
      cases assump_54
      case intro assump_63 assump_64 =>
        cases assump_64
        case intro assump_67 assump_68 =>
          apply False.elim assump_67


variable (p2 p3 p6 p4 : Prop)
theorem file19_81907 : (((((p2 → p6) → False) → False) ∧ (((False → p4) → False) ∧ ((True → True) ∨ (p2 → True)))) → ((((False ∧ p6) ∨ (p3 → False)) → False) ∨ (((True → False) → False) ∨ ((p2 ∨ True) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        case inr assump_16 =>
          have assump_53 : (False → p4) := by
            intro assump_27
            apply False.elim assump_27
          let assump_26 := assump_6 assump_53
          apply False.elim assump_26
      case inr assump_11 =>
        apply Or.inl
        intro assump_35
        cases assump_35
        case inl assump_36 =>
          cases assump_36
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
        case inr assump_37 =>
          have assump_54 : (False → p4) := by
            intro assump_47
            apply False.elim assump_47
          let assump_46 := assump_6 assump_54
          apply False.elim assump_46


variable (p4 p0 p2 p5 : Prop)
theorem file19_83225 : (((((p4 ∧ p5) ∧ (p0 → p4)) ∨ ((p2 ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : (((p4 ∧ p5) ∧ (p0 → p4)) ∨ ((p2 ∧ False) → False)) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p5 p1 p4 p3 p7 : Prop)
theorem file19_83643 : (((((False → True) → False) → ((False ∧ p7) → False)) ∨ (((p5 → p6) ∧ (p7 ∨ p3)) → False)) ∨ ((((p5 ∧ p4) → (p3 → False)) → ((p1 ∨ p6) ∨ (True ∧ True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    apply False.elim assump_7


variable (p6 p5 p0 p4 p2 p7 p1 p3 : Prop)
theorem file19_84023 : (((((p3 ∧ p5) → (p1 ∨ p7)) ∨ ((p4 ∨ p6) ∨ (p3 ∨ False))) ∨ (((p4 → False) → (p4 → False)) ∧ ((p4 → False) ∧ (p7 → p2)))) → ((((p6 → False) ∧ (p1 ∧ p0)) ∨ ((p7 ∧ p1) → (p5 ∧ p1))) → (((False ∧ p1) ∨ (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  case inr assump_5 =>
    cases assump_2
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_1
          case inl assump_24 =>
            cases assump_24
            case inl assump_26 =>
              have assump_179 : True := by
                apply True.intro
              let assump_34 := assump_5 assump_179
              apply False.elim assump_34
            case inr assump_27 =>
              cases assump_27
              case inl assump_38 =>
                cases assump_38
                case inl assump_40 =>
                  have assump_180 : True := by
                    apply True.intro
                  let assump_48 := assump_5 assump_180
                  apply False.elim assump_48
                case inr assump_41 =>
                  have assump_181 : p6 := by
                    exact assump_41
                  let assump_57 := assump_14 assump_181
                  apply False.elim assump_57
              case inr assump_39 =>
                cases assump_39
                case inl assump_61 =>
                  have assump_182 : True := by
                    apply True.intro
                  let assump_69 := assump_5 assump_182
                  apply False.elim assump_69
                case inr assump_62 =>
                  apply False.elim assump_62
          case inr assump_25 =>
            cases assump_25
            case intro assump_75 assump_76 =>
              cases assump_76
              case intro assump_79 assump_80 =>
                have assump_183 : True := by
                  apply True.intro
                let assump_101 := assump_5 assump_183
                apply False.elim assump_101
    case inr assump_13 =>
      cases assump_1
      case inl assump_107 =>
        cases assump_107
        case inl assump_109 =>
          have assump_184 : True := by
            apply True.intro
          let assump_115 := assump_5 assump_184
          apply False.elim assump_115
        case inr assump_110 =>
          cases assump_110
          case inl assump_119 =>
            cases assump_119
            case inl assump_121 =>
              have assump_185 : True := by
                apply True.intro
              let assump_127 := assump_5 assump_185
              apply False.elim assump_127
            case inr assump_122 =>
              have assump_186 : True := by
                apply True.intro
              let assump_135 := assump_5 assump_186
              apply False.elim assump_135
          case inr assump_120 =>
            cases assump_120
            case inl assump_139 =>
              have assump_187 : True := by
                apply True.intro
              let assump_145 := assump_5 assump_187
              apply False.elim assump_145
            case inr assump_140 =>
              apply False.elim assump_140
      case inr assump_108 =>
        cases assump_108
        case intro assump_151 assump_152 =>
          cases assump_152
          case intro assump_155 assump_156 =>
            have assump_188 : True := by
              apply True.intro
            let assump_175 := assump_5 assump_188
            apply False.elim assump_175


variable (p5 p0 p4 p2 p7 p3 : Prop)
theorem file19_87777 : (((((p7 ∨ True) → False) ∧ ((p7 ∨ p3) ∧ (False → False))) → False) ∨ ((((p0 → p5) ∧ (p7 ∨ p7)) ∨ ((p4 → False) ∨ (p2 ∨ p5))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : (p7 ∨ True) := by
          apply Or.inl
          exact assump_8
        let assump_16 := assump_2 assump_30
        apply False.elim assump_16
      case inr assump_9 =>
        have assump_31 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_26 := assump_2 assump_31
        apply False.elim assump_26


variable (p4 p5 p7 p2 p6 p1 p3 p0 : Prop)
theorem file19_88539 : ((((((p6 ∧ p2) → (p5 ∨ p4)) ∧ ((p2 → p0) ∧ (False ∧ p7))) ∧ (((p0 ∨ p3) ∨ (p1 → False)) → ((p6 ∧ p7) → (p4 → False)))) ∧ ((((p5 → False) ∧ (p6 ∨ p5)) → False) ∧ (((p4 → False) → (p7 → p3)) → ((False → p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p5 p1 p0 p4 p7 p6 p2 p3 : Prop)
theorem file19_89193 : (((((p5 → False) ∨ (p0 → False)) → ((p0 ∧ p5) → (p1 ∨ p7))) ∨ (((p4 → False) → (p3 ∨ p4)) → False)) ∨ ((((p7 → p2) ∨ (p0 ∧ p6)) → ((p5 → False) ∧ (p0 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_13
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_13
    case inl assump_21 =>
      have assump_35 : p5 := by
        exact assump_16
      let assump_25 := assump_21 assump_35
      apply False.elim assump_25
    case inr assump_22 =>
      have assump_36 : p0 := by
        exact assump_15
      let assump_31 := assump_22 assump_36
      apply False.elim assump_31


variable (p1 p0 p3 : Prop)
theorem file19_89877 : (((((False ∨ p3) ∨ (False → p1)) ∨ ((p0 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : (((False ∨ p3) ∨ (False → p1)) ∨ ((p0 → False) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p4 p0 p6 p5 p3 p1 p7 : Prop)
theorem file19_90273 : (((((True → False) ∧ (p4 ∧ p6)) → ((False → p2) → False)) → (((p6 → True) ∨ (p4 ∧ p3)) ∨ ((p1 → False) ∨ (p4 → False)))) ∨ ((((p6 → p0) ∧ (p1 → p1)) → False) → (((p0 ∧ p0) → (False → False)) → ((p5 → False) ∧ (p7 ∧ p7))))) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  apply Or.inl
  intro assump_8
  apply True.intro


variable (p7 p6 p1 p3 : Prop)
theorem file19_90654 : ((((((p7 ∨ False) ∨ (p3 → False)) ∨ ((True ∧ p6) → (p6 → False))) → (((p1 → False) ∧ (False ∧ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p7 ∨ False) ∨ (p3 → False)) ∨ ((True ∧ p6) → (p6 → False))) → (((p1 → False) ∧ (False ∧ True)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p4 p6 p3 : Prop)
theorem file19_91248 : ((((((p0 ∧ p3) ∧ (p4 ∧ p6)) ∧ ((p3 ∧ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p0 ∧ p3) ∧ (p4 ∧ p6)) ∧ ((p3 ∧ p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            have assump_32 : (p3 ∧ p4) := by
              apply And.intro
              exact assump_11
              exact assump_16
            let assump_24 := assump_7 assump_32
            apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p3 p6 p7 p4 p0 p5 : Prop)
theorem file19_92049 : (((((False ∧ p0) ∧ (p7 ∨ p7)) ∧ ((p1 → False) → (True → False))) → (((p4 ∨ p6) ∨ (False ∧ True)) → False)) ∨ ((((p5 → False) → False) → False) ∨ (((False ∨ p3) → False) ∨ ((p1 → p7) → (p7 → p0))))) := by
  apply Or.inl
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
            apply False.elim assump_13
    case inr assump_6 =>
      cases assump_1
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
  case inr assump_4 =>
    cases assump_4
    case intro assump_27 assump_28 =>
      apply False.elim assump_27


variable (p3 p6 p5 p0 p7 : Prop)
theorem file19_93051 : ((((((p5 ∨ p0) → False) ∧ ((p6 ∨ p3) → False)) → (((p6 → False) ∨ (p5 ∨ p7)) ∨ ((p6 → True) → False))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 ∨ p0) → False) ∧ ((p6 ∨ p3) → False)) → (((p6 → False) ∨ (p5 ∨ p7)) ∨ ((p6 → True) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      have assump_24 : (p6 ∨ p3) := by
        apply Or.inl
        exact assump_12
      let assump_16 := assump_7 assump_24
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p4 p6 p3 : Prop)
theorem file19_93736 : ((((((p1 → False) → (p3 → False)) → ((p5 ∧ p4) → False)) → (((p6 → p1) ∧ (False ∧ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) → (p3 → False)) → ((p5 ∧ p4) → False)) → (((p6 → p1) ∧ (False ∧ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p6 p4 p1 p5 p3 p0 : Prop)
theorem file19_94311 : (((((p3 → False) → (p1 ∧ p6)) → False) ∧ (((p3 → False) → False) ∧ ((p6 → p6) ∧ (p2 ∧ p4)))) → ((((p5 → p5) → False) → False) ∨ (((p0 → p4) → (p6 → p3)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          have assump_30 : (p5 → p5) := by
            intro assump_24
            exact assump_24
          let assump_23 := assump_20 assump_30
          apply False.elim assump_23


variable (p5 p0 p6 p4 p7 p3 p2 : Prop)
theorem file19_95026 : (((((p5 ∨ p7) ∨ (p5 → p3)) → ((p3 ∧ p2) → (p3 ∧ p7))) → (((p7 ∧ p0) → False) ∨ ((p2 → False) ∧ (p7 → p6)))) → ((((p4 ∧ p7) ∧ (p2 ∧ p0)) → False) ∨ (((p2 → False) → False) → ((p0 ∧ True) ∧ (p6 → p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        have assump_79 : (((p5 ∨ p7) ∨ (p5 → p3)) → ((p3 ∧ p2) → (p3 ∧ p7))) := by
          intro assump_24
          intro assump_25
          apply And.intro
          cases assump_25
          case intro assump_26 assump_27 =>
            cases assump_24
            case inl assump_32 =>
              cases assump_32
              case inl assump_34 =>
                exact assump_26
              case inr assump_35 =>
                exact assump_26
            case inr assump_33 =>
              exact assump_26
          cases assump_25
          case intro assump_42 assump_43 =>
            cases assump_24
            case inl assump_48 =>
              cases assump_48
              case inl assump_50 =>
                exact assump_8
              case inr assump_51 =>
                exact assump_51
            case inr assump_49 =>
              exact assump_8
        let assump_23 := assump_1 assump_79
        cases assump_23
        case inl assump_59 =>
          have assump_80 : (p7 ∧ p0) := by
            apply And.intro
            exact assump_8
            exact assump_14
          let assump_63 := assump_59 assump_80
          apply False.elim assump_63
        case inr assump_60 =>
          cases assump_60
          case intro assump_67 assump_68 =>
            have assump_81 : p2 := by
              exact assump_13
            let assump_75 := assump_67 assump_81
            apply False.elim assump_75


variable (p4 p6 p3 : Prop)
theorem file19_96948 : (((((p4 ∧ p6) ∧ (p6 → False)) → ((True ∨ p4) ∧ (p6 → p3))) → False) → False) := by
  intro assump_30
  have assump_65 : (((p4 ∧ p6) ∧ (p6 → False)) → ((True ∨ p4) ∧ (p6 → p3))) := by
    intro assump_34
    apply And.intro
    cases assump_34
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        apply Or.inl
        apply True.intro
    intro assump_45
    cases assump_34
    case intro assump_48 assump_49 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        have assump_66 : p6 := by
          exact assump_51
        let assump_58 := assump_49 assump_66
        apply False.elim assump_58
  let assump_33 := assump_30 assump_65
  apply False.elim assump_33


variable (p2 p1 p0 p4 : Prop)
theorem file19_97739 : (((((False → p0) → (p1 → p1)) ∨ ((p2 → p4) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((False → p0) → (p1 → p1)) ∨ ((p2 → p4) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p5 p6 p3 p2 p4 : Prop)
theorem file19_98108 : (((((True → False) ∧ (False ∨ p3)) ∧ ((p5 → False) ∨ (p4 → False))) → (((True ∨ p4) ∨ (p5 ∨ p1)) ∧ ((p4 ∨ p2) → False))) ∨ ((((p6 → False) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        cases assump_3
        case inl assump_14 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
  intro assump_20
  cases assump_20
  case inl assump_21 =>
    cases assump_1
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_28
        case inl assump_31 =>
          apply False.elim assump_31
        case inr assump_32 =>
          cases assump_26
          case inl assump_37 =>
            have assump_85 : True := by
              apply True.intro
            let assump_43 := assump_27 assump_85
            apply False.elim assump_43
          case inr assump_38 =>
            have assump_86 : p4 := by
              exact assump_21
            let assump_49 := assump_38 assump_86
            apply False.elim assump_49
  case inr assump_22 =>
    cases assump_1
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        cases assump_58
        case inl assump_61 =>
          apply False.elim assump_61
        case inr assump_62 =>
          cases assump_56
          case inl assump_67 =>
            have assump_87 : True := by
              apply True.intro
            let assump_73 := assump_57 assump_87
            apply False.elim assump_73
          case inr assump_68 =>
            have assump_88 : True := by
              apply True.intro
            let assump_81 := assump_57 assump_88
            apply False.elim assump_81


variable (p6 p2 : Prop)
theorem file19_100200 : ((((((False → False) → False) ∧ ((False → False) → (p2 ∧ p6))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False → False) → False) ∧ ((False → False) → (p2 ∧ p6))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_30 : (False → False) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_6 assump_30
      apply False.elim assump_19
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p4 p3 p6 p0 : Prop)
theorem file19_100783 : (((((p6 → False) → False) → ((p3 → True) ∧ (p1 → False))) → False) → ((((p6 ∧ p1) → False) ∨ ((True ∧ p0) ∨ (p4 ∨ p6))) → (((True ∧ p6) ∨ (p4 ∨ p1)) → ((False ∧ p1) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p4 p5 p1 p0 p3 p2 p6 : Prop)
theorem file19_101202 : (((((p5 ∨ p1) → False) ∨ ((False ∧ p4) ∧ (p5 → p2))) ∧ (((p6 ∨ p1) → False) → False)) → ((((p3 ∧ p6) ∧ (p0 ∨ False)) → ((p0 ∧ False) → (True ∨ p3))) ∨ (((p3 → False) → False) ∧ ((p0 → False) → (True ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      cases assump_11
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_20


variable (p0 p3 p1 p5 p2 p4 : Prop)
theorem file19_101938 : (((((False → False) → False) → ((False → False) ∧ (p4 ∧ False))) → False) → ((((p3 → False) ∧ (p0 → False)) ∧ ((True → False) ∧ (p1 → False))) ∨ (((p1 ∨ p3) ∨ (p1 → p2)) → ((p0 → p5) ∨ (True ∧ p4))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  apply And.intro
  intro assump_4
  have assump_123 : (((False → False) → False) → ((False → False) ∧ (p4 ∧ False))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    apply False.elim assump_10
    apply And.intro
    have assump_124 : (False → False) := by
      intro assump_16
      apply False.elim assump_16
    let assump_15 := assump_9 assump_124
    apply False.elim assump_15
    have assump_125 : (False → False) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_9 assump_125
    apply False.elim assump_24
  let assump_8 := assump_1 assump_123
  apply False.elim assump_8
  intro assump_34
  have assump_126 : (((False → False) → False) → ((False → False) ∧ (p4 ∧ False))) := by
    intro assump_39
    apply And.intro
    intro assump_40
    apply False.elim assump_40
    apply And.intro
    have assump_127 : (False → False) := by
      intro assump_46
      apply False.elim assump_46
    let assump_45 := assump_39 assump_127
    apply False.elim assump_45
    have assump_128 : (False → False) := by
      intro assump_55
      apply False.elim assump_55
    let assump_54 := assump_39 assump_128
    apply False.elim assump_54
  let assump_38 := assump_1 assump_126
  apply False.elim assump_38
  apply And.intro
  intro assump_64
  have assump_129 : (((False → False) → False) → ((False → False) ∧ (p4 ∧ False))) := by
    intro assump_68
    apply And.intro
    intro assump_69
    apply False.elim assump_69
    apply And.intro
    have assump_130 : (False → False) := by
      intro assump_75
      apply False.elim assump_75
    let assump_74 := assump_68 assump_130
    apply False.elim assump_74
    have assump_131 : (False → False) := by
      intro assump_84
      apply False.elim assump_84
    let assump_83 := assump_68 assump_131
    apply False.elim assump_83
  let assump_67 := assump_1 assump_129
  apply False.elim assump_67
  intro assump_93
  have assump_132 : (((False → False) → False) → ((False → False) ∧ (p4 ∧ False))) := by
    intro assump_98
    apply And.intro
    intro assump_99
    apply False.elim assump_99
    apply And.intro
    have assump_133 : (False → False) := by
      intro assump_105
      apply False.elim assump_105
    let assump_104 := assump_98 assump_133
    apply False.elim assump_104
    have assump_134 : (False → False) := by
      intro assump_114
      apply False.elim assump_114
    let assump_113 := assump_98 assump_134
    apply False.elim assump_113
  let assump_97 := assump_1 assump_132
  apply False.elim assump_97


variable (p2 p6 p0 p4 p3 p5 : Prop)
theorem file19_104813 : (((((False ∨ False) ∨ (True ∧ p2)) ∧ ((False → p3) ∧ (p3 ∨ p0))) ∨ (((p2 ∧ p5) ∧ (True ∨ False)) → ((p6 ∧ p6) ∨ (p3 ∨ p5)))) ∨ ((((p4 ∧ p6) → False) → False) ∧ (((p5 → p3) → (True → False)) ∨ ((p0 → False) ∧ (p6 ∨ p5))))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        apply Or.inr
        apply Or.inr
        exact assump_5
      case inr assump_11 =>
        apply False.elim assump_11


variable (p1 p4 p0 p2 p7 p3 : Prop)
theorem file19_105431 : ((((((p4 ∧ p1) → (p3 ∧ p3)) → ((True ∧ p0) → (p3 → p3))) ∨ (((p2 → False) ∨ (p7 ∧ p7)) ∧ ((p7 ∨ True) → False))) → False) → False) := by
  intro assump_5
  have assump_25 : ((((p4 ∧ p1) → (p3 ∧ p3)) → ((True ∧ p0) → (p3 → p3))) ∨ (((p2 → False) ∨ (p7 ∧ p7)) ∧ ((p7 ∨ True) → False))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_10
    case intro assump_14 assump_15 =>
      exact assump_11
  let assump_8 := assump_5 assump_25
  apply False.elim assump_8


variable (p0 p5 p2 : Prop)
theorem file19_105993 : (((((False → p2) → False) → ((p2 ∧ False) ∨ (p0 → p5))) → False) → False) := by
  intro assump_1
  have assump_22 : (((False → p2) → False) → ((p2 ∧ False) ∨ (p0 → p5))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_23 : (False → p2) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p4 p1 p3 p2 : Prop)
theorem file19_106512 : (((((p5 ∧ p2) → False) ∧ ((p1 ∨ True) ∨ (p4 → False))) ∧ (((False → False) → False) ∧ ((p3 ∨ p2) ∧ (False → False)))) → False) := by
  intro assump_35
  cases assump_35
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_39
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          cases assump_37
          case intro assump_48 assump_49 =>
            cases assump_49
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                have assump_154 : (False → False) := by
                  intro assump_63
                  apply False.elim assump_63
                let assump_62 := assump_48 assump_154
                apply False.elim assump_62
              case inr assump_55 =>
                have assump_155 : (False → False) := by
                  intro assump_76
                  apply False.elim assump_76
                let assump_75 := assump_48 assump_155
                apply False.elim assump_75
        case inr assump_45 =>
          cases assump_37
          case intro assump_84 assump_85 =>
            cases assump_85
            case intro assump_88 assump_89 =>
              cases assump_88
              case inl assump_90 =>
                have assump_156 : (False → False) := by
                  intro assump_99
                  apply False.elim assump_99
                let assump_98 := assump_84 assump_156
                apply False.elim assump_98
              case inr assump_91 =>
                have assump_157 : (False → False) := by
                  intro assump_112
                  apply False.elim assump_112
                let assump_111 := assump_84 assump_157
                apply False.elim assump_111
      case inr assump_43 =>
        cases assump_37
        case intro assump_120 assump_121 =>
          cases assump_121
          case intro assump_124 assump_125 =>
            cases assump_124
            case inl assump_126 =>
              have assump_158 : (False → False) := by
                intro assump_135
                apply False.elim assump_135
              let assump_134 := assump_120 assump_158
              apply False.elim assump_134
            case inr assump_127 =>
              have assump_159 : (False → False) := by
                intro assump_148
                apply False.elim assump_148
              let assump_147 := assump_120 assump_159
              apply False.elim assump_147


variable (p7 p6 p1 p4 p2 p0 p3 : Prop)
theorem file19_109118 : (((((p0 → False) → (p7 ∧ True)) → ((p6 ∧ False) ∨ (True ∧ True))) → False) → ((((p3 ∧ p1) ∧ (p6 ∨ p4)) ∧ ((p2 → False) ∧ (p2 ∨ p1))) ∨ (((False ∨ p4) → False) ∧ ((p4 ∨ p0) → False)))) := by
  intro assump_1
  apply Or.inr
  apply And.intro
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply False.elim assump_5
  case inr assump_6 =>
    have assump_42 : (((p0 → False) → (p7 ∧ True)) → ((p6 ∧ False) ∨ (True ∧ True))) := by
      intro assump_13
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_12 := assump_1 assump_42
    apply False.elim assump_12
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    have assump_43 : (((p0 → False) → (p7 ∧ True)) → ((p6 ∧ False) ∨ (True ∧ True))) := by
      intro assump_26
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_25 := assump_1 assump_43
    apply False.elim assump_25
  case inr assump_21 =>
    have assump_44 : (((p0 → False) → (p7 ∧ True)) → ((p6 ∧ False) ∨ (True ∧ True))) := by
      intro assump_36
      apply Or.inr
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_35 := assump_1 assump_44
    apply False.elim assump_35


variable (p6 p5 p0 p2 p4 p1 p3 p7 : Prop)
theorem file19_110431 : (((((p2 → False) ∧ (p5 → False)) → False) ∧ (((p1 → False) → False) ∧ ((p6 ∧ p5) ∨ (p5 ∧ p7)))) → ((((p6 ∨ p3) ∧ (p2 ∨ True)) → ((p2 ∧ p2) ∨ (p4 → False))) → (((p5 ∨ p3) → (False → True)) ∨ ((p7 ∨ p7) ∨ (p0 ∧ p5))))) := by
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_16
      case inl assump_19 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          intro assump_28
          apply True.intro
      case inr assump_20 =>
        cases assump_20
        case intro assump_29 assump_30 =>
          apply Or.inl
          intro assump_35
          intro assump_36
          apply True.intro


variable (p3 p2 p4 p5 p1 p7 p0 : Prop)
theorem file19_111276 : (((((False → False) ∧ (p3 ∨ p5)) ∧ ((p0 ∨ p4) ∨ (p2 ∧ p1))) → (((p7 → False) → False) → False)) → ((((p3 ∨ p7) ∨ (p5 → False)) → ((p3 ∨ True) ∨ (True → False))) ∨ (((p5 → False) ∧ (False ∨ p3)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      exact assump_7
    case inr assump_8 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p5 p0 p6 p1 p2 : Prop)
theorem file19_111900 : (((((p5 ∧ p1) → False) → ((p5 → p2) ∨ (p2 ∨ p0))) ∧ (((p6 ∧ True) ∨ (p6 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : ((p6 ∧ True) ∨ (p6 ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p7 p2 p1 p5 p0 p4 p6 : Prop)
theorem file19_112322 : (((((p1 ∨ p2) → (p7 → p7)) → False) ∧ (((p7 → False) → (True ∨ True)) → False)) → ((((False → p1) → False) ∨ ((p1 ∧ p6) ∧ (p4 ∧ p0))) → (((True → False) ∨ (p5 ∧ p2)) ∧ ((p0 → p1) ∧ (p4 → False))))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  cases assump_6
  case inl assump_7 =>
    cases assump_5
    case intro assump_11 assump_12 =>
      apply Or.inl
      intro assump_17
      have assump_144 : ((p7 → False) → (True ∨ True)) := by
        intro assump_21
        apply Or.inl
        apply True.intro
      let assump_20 := assump_12 assump_144
      apply False.elim assump_20
  case inr assump_8 =>
    cases assump_8
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_28
        case intro assump_35 assump_36 =>
          cases assump_5
          case intro assump_41 assump_42 =>
            apply Or.inl
            intro assump_47
            have assump_145 : ((p7 → False) → (True ∨ True)) := by
              intro assump_51
              apply Or.inl
              apply True.intro
            let assump_50 := assump_42 assump_145
            apply False.elim assump_50
  apply And.intro
  intro assump_57
  cases assump_6
  case inl assump_60 =>
    cases assump_5
    case intro assump_64 assump_65 =>
      have assump_146 : ((p7 → False) → (True ∨ True)) := by
        intro assump_71
        apply Or.inl
        apply True.intro
      let assump_70 := assump_65 assump_146
      apply False.elim assump_70
  case inr assump_61 =>
    cases assump_61
    case intro assump_77 assump_78 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_78
        case intro assump_85 assump_86 =>
          cases assump_5
          case intro assump_91 assump_92 =>
            exact assump_79
  intro assump_97
  cases assump_6
  case inl assump_100 =>
    cases assump_5
    case intro assump_104 assump_105 =>
      have assump_147 : ((p7 → False) → (True ∨ True)) := by
        intro assump_111
        apply Or.inl
        apply True.intro
      let assump_110 := assump_105 assump_147
      apply False.elim assump_110
  case inr assump_101 =>
    cases assump_101
    case intro assump_117 assump_118 =>
      cases assump_117
      case intro assump_119 assump_120 =>
        cases assump_118
        case intro assump_125 assump_126 =>
          cases assump_5
          case intro assump_131 assump_132 =>
            have assump_148 : ((p7 → False) → (True ∨ True)) := by
              intro assump_138
              apply Or.inl
              apply True.intro
            let assump_137 := assump_132 assump_148
            apply False.elim assump_137


variable (p4 p6 p5 p3 p0 p7 : Prop)
theorem file19_115077 : (((((p0 → False) ∨ (False ∨ p7)) ∧ ((p4 ∧ p6) ∧ (True → False))) ∧ (((p5 → True) ∨ (p3 → False)) → False)) → ((((p5 ∨ p4) ∧ (p4 ∧ p5)) ∧ ((True ∨ False) ∨ (False ∨ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          cases assump_4
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_1
              case intro assump_23 assump_24 =>
                cases assump_23
                case intro assump_25 assump_26 =>
                  cases assump_25
                  case inl assump_27 =>
                    cases assump_26
                    case intro assump_31 assump_32 =>
                      cases assump_31
                      case intro assump_33 assump_34 =>
                        have assump_245 : ((p5 → True) ∨ (p3 → False)) := by
                          apply Or.inl
                          intro assump_44
                          apply True.intro
                        let assump_43 := assump_24 assump_245
                        apply False.elim assump_43
                  case inr assump_28 =>
                    cases assump_28
                    case inl assump_48 =>
                      apply False.elim assump_48
                    case inr assump_49 =>
                      cases assump_26
                      case intro assump_54 assump_55 =>
                        cases assump_54
                        case intro assump_56 assump_57 =>
                          have assump_246 : ((p5 → True) ∨ (p3 → False)) := by
                            apply Or.inl
                            intro assump_67
                            apply True.intro
                          let assump_66 := assump_24 assump_246
                          apply False.elim assump_66
            case inr assump_20 =>
              apply False.elim assump_20
          case inr assump_18 =>
            cases assump_18
            case inl assump_73 =>
              apply False.elim assump_73
            case inr assump_74 =>
              cases assump_1
              case intro assump_79 assump_80 =>
                cases assump_79
                case intro assump_81 assump_82 =>
                  cases assump_81
                  case inl assump_83 =>
                    cases assump_82
                    case intro assump_87 assump_88 =>
                      cases assump_87
                      case intro assump_89 assump_90 =>
                        have assump_247 : ((p5 → True) ∨ (p3 → False)) := by
                          apply Or.inl
                          intro assump_100
                          apply True.intro
                        let assump_99 := assump_80 assump_247
                        apply False.elim assump_99
                  case inr assump_84 =>
                    cases assump_84
                    case inl assump_104 =>
                      apply False.elim assump_104
                    case inr assump_105 =>
                      cases assump_82
                      case intro assump_110 assump_111 =>
                        cases assump_110
                        case intro assump_112 assump_113 =>
                          have assump_248 : ((p5 → True) ∨ (p3 → False)) := by
                            apply Or.inl
                            intro assump_123
                            apply True.intro
                          let assump_122 := assump_80 assump_248
                          apply False.elim assump_122
      case inr assump_8 =>
        cases assump_6
        case intro assump_129 assump_130 =>
          cases assump_4
          case inl assump_135 =>
            cases assump_135
            case inl assump_137 =>
              cases assump_1
              case intro assump_141 assump_142 =>
                cases assump_141
                case intro assump_143 assump_144 =>
                  cases assump_143
                  case inl assump_145 =>
                    cases assump_144
                    case intro assump_149 assump_150 =>
                      cases assump_149
                      case intro assump_151 assump_152 =>
                        have assump_249 : ((p5 → True) ∨ (p3 → False)) := by
                          apply Or.inl
                          intro assump_162
                          apply True.intro
                        let assump_161 := assump_142 assump_249
                        apply False.elim assump_161
                  case inr assump_146 =>
                    cases assump_146
                    case inl assump_166 =>
                      apply False.elim assump_166
                    case inr assump_167 =>
                      cases assump_144
                      case intro assump_172 assump_173 =>
                        cases assump_172
                        case intro assump_174 assump_175 =>
                          have assump_250 : ((p5 → True) ∨ (p3 → False)) := by
                            apply Or.inl
                            intro assump_185
                            apply True.intro
                          let assump_184 := assump_142 assump_250
                          apply False.elim assump_184
            case inr assump_138 =>
              apply False.elim assump_138
          case inr assump_136 =>
            cases assump_136
            case inl assump_191 =>
              apply False.elim assump_191
            case inr assump_192 =>
              cases assump_1
              case intro assump_197 assump_198 =>
                cases assump_197
                case intro assump_199 assump_200 =>
                  cases assump_199
                  case inl assump_201 =>
                    cases assump_200
                    case intro assump_205 assump_206 =>
                      cases assump_205
                      case intro assump_207 assump_208 =>
                        have assump_251 : ((p5 → True) ∨ (p3 → False)) := by
                          apply Or.inl
                          intro assump_218
                          apply True.intro
                        let assump_217 := assump_198 assump_251
                        apply False.elim assump_217
                  case inr assump_202 =>
                    cases assump_202
                    case inl assump_222 =>
                      apply False.elim assump_222
                    case inr assump_223 =>
                      cases assump_200
                      case intro assump_228 assump_229 =>
                        cases assump_228
                        case intro assump_230 assump_231 =>
                          have assump_252 : ((p5 → True) ∨ (p3 → False)) := by
                            apply Or.inl
                            intro assump_241
                            apply True.intro
                          let assump_240 := assump_198 assump_252
                          apply False.elim assump_240


variable (p7 p5 p2 p0 p1 : Prop)
theorem file19_122311 : ((((((p2 → False) → (p7 ∧ p1)) → False) → False) ∧ ((((p0 ∨ False) → False) → ((p0 → False) ∧ (p0 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((p0 ∨ False) → False) → ((p0 → False) ∧ (p0 → p5))) := by
      intro assump_9
      apply And.intro
      intro assump_10
      have assump_32 : (p0 ∨ False) := by
        apply Or.inl
        exact assump_10
      let assump_15 := assump_9 assump_32
      apply False.elim assump_15
      intro assump_19
      have assump_33 : (p0 ∨ False) := by
        apply Or.inl
        exact assump_19
      let assump_24 := assump_9 assump_33
      apply False.elim assump_24
    let assump_8 := assump_3 assump_31
    apply False.elim assump_8


variable (p4 p7 p6 p5 p0 : Prop)
theorem file19_123128 : (((((True → True) ∨ (p7 ∧ p6)) ∧ ((p5 ∧ p5) → (p7 ∨ p0))) → False) → ((((False ∧ False) ∧ (p7 ∨ p4)) → False) ∨ (((False → False) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_7


variable (p0 p5 p4 p2 : Prop)
theorem file19_123525 : (((((p2 ∧ True) ∨ (p2 ∧ True)) → ((p4 → False) → False)) ∧ (((p4 → p4) → False) ∧ ((p0 → p0) ∨ (p2 → p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_32 : (p4 → p4) := by
          intro assump_16
          exact assump_16
        let assump_15 := assump_6 assump_32
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_33 : (p4 → p4) := by
          intro assump_26
          exact assump_26
        let assump_25 := assump_6 assump_33
        apply False.elim assump_25


variable (p4 p3 p7 p2 p0 p5 p1 : Prop)
theorem file19_124255 : ((((((p0 → False) ∧ (p1 ∧ p4)) ∨ ((False → False) → False)) ∧ (((p3 → False) ∧ (False ∧ p0)) ∧ ((p0 → p3) → (p7 ∨ p2)))) ∨ ((((True → p5) ∨ (p7 → False)) ∧ ((p3 ∧ p1) ∧ (p7 ∨ p1))) ∧ (((p4 → False) ∧ (p0 → False)) ∧ ((p3 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  apply False.elim assump_24
      case inr assump_7 =>
        cases assump_5
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              apply False.elim assump_36
  case inr assump_3 =>
    cases assump_3
    case intro assump_40 assump_41 =>
      cases assump_40
      case intro assump_42 assump_43 =>
        cases assump_42
        case inl assump_44 =>
          cases assump_43
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              cases assump_49
              case inl assump_56 =>
                cases assump_41
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    have assump_138 : (p3 → True) := by
                      intro assump_71
                      apply True.intro
                    let assump_70 := assump_61 assump_138
                    apply False.elim assump_70
              case inr assump_57 =>
                cases assump_41
                case intro assump_77 assump_78 =>
                  cases assump_77
                  case intro assump_79 assump_80 =>
                    have assump_139 : (p3 → True) := by
                      intro assump_88
                      apply True.intro
                    let assump_87 := assump_78 assump_139
                    apply False.elim assump_87
        case inr assump_45 =>
          cases assump_43
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_95
              case inl assump_102 =>
                cases assump_41
                case intro assump_106 assump_107 =>
                  cases assump_106
                  case intro assump_108 assump_109 =>
                    have assump_140 : (p3 → True) := by
                      intro assump_117
                      apply True.intro
                    let assump_116 := assump_107 assump_140
                    apply False.elim assump_116
              case inr assump_103 =>
                cases assump_41
                case intro assump_123 assump_124 =>
                  cases assump_123
                  case intro assump_125 assump_126 =>
                    have assump_141 : (p3 → True) := by
                      intro assump_134
                      apply True.intro
                    let assump_133 := assump_124 assump_141
                    apply False.elim assump_133


