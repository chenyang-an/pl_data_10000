variable (p6 p5 p4 p7 : Prop)
theorem file85_38 : ((((((False → False) → False) → False) ∨ (((p4 ∨ p7) → False) ∨ ((p6 ∨ p5) ∧ (p4 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p4 ∨ p7) → False) ∨ ((p6 ∨ p5) ∧ (p4 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p3 p6 p5 p2 p0 p1 : Prop)
theorem file85_617 : (((((p4 → p1) ∨ (p0 → False)) ∧ ((p1 ∧ p2) → False)) → (((p4 → p3) ∨ (p6 → p1)) ∧ ((p4 ∨ p2) ∨ (p2 → False)))) → ((((True ∨ p0) → False) ∧ ((False ∧ p5) ∧ (True → False))) → False)) := by
  intro assump_20
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_23
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply False.elim assump_28


variable (p2 p6 p7 p5 p3 p1 p4 : Prop)
theorem file85_1113 : (((((p7 ∧ p5) ∨ (p6 → False)) → ((p7 → p2) → (p3 ∧ p4))) → (((False ∧ p7) ∧ (p4 → False)) → False)) ∨ ((((p7 → False) → (p4 ∧ p2)) → ((p7 → False) → (p3 ∧ p5))) ∧ (((p1 ∨ True) ∧ (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p5 p3 p4 p1 p2 : Prop)
theorem file85_1567 : (((((p2 ∨ p4) ∨ (False → False)) → False) ∧ (((p3 ∧ False) → False) → False)) → ((((True ∨ p5) → (p5 ∨ p1)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_22 : ((p3 ∧ False) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    let assump_11 := assump_6 assump_22
    apply False.elim assump_11


variable (p6 p7 p5 p4 p3 p1 p0 p2 : Prop)
theorem file85_2091 : (((((p3 ∧ p3) ∧ (True ∧ p6)) → ((p5 → p1) ∨ (p7 ∧ p7))) → (((p1 → False) ∨ (p2 ∧ False)) ∧ ((True ∧ p6) ∧ (p6 → p3)))) → ((((True ∧ True) ∨ (True → False)) ∨ ((True ∨ p2) ∨ (p4 ∧ p2))) ∨ (((p5 → p5) ∧ (p2 → p1)) ∧ ((p0 ∨ p3) ∧ (p0 ∧ p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p6 p3 p5 p2 p0 p7 : Prop)
theorem file85_2516 : (((((p7 → False) → False) ∨ ((True ∨ p0) ∧ (p6 → False))) ∧ (((p7 → p6) → (p6 ∨ p6)) ∨ ((p6 ∧ p0) ∧ (False → False)))) → ((((p5 ∨ True) → False) → False) ∨ (((p6 ∧ p5) ∨ (p3 ∨ p2)) ∧ ((p0 ∧ False) ∧ (p3 ∧ p0))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        have assump_104 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_15 := assump_12 assump_104
        apply False.elim assump_15
      case inr assump_9 =>
        cases assump_9
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply Or.inl
            intro assump_29
            have assump_105 : (p5 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_32 := assump_29 assump_105
            apply False.elim assump_32
    case inr assump_5 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_3
          case inl assump_44 =>
            apply Or.inl
            intro assump_48
            have assump_106 : (p5 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_51 := assump_48 assump_106
            apply False.elim assump_51
          case inr assump_45 =>
            cases assump_45
            case intro assump_55 assump_56 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                apply Or.inl
                intro assump_65
                have assump_107 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_68 := assump_65 assump_107
                apply False.elim assump_68
        case inr assump_39 =>
          cases assump_3
          case inl assump_76 =>
            apply Or.inl
            intro assump_80
            have assump_108 : (p5 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_83 := assump_80 assump_108
            apply False.elim assump_83
          case inr assump_77 =>
            cases assump_77
            case intro assump_87 assump_88 =>
              cases assump_87
              case intro assump_89 assump_90 =>
                apply Or.inl
                intro assump_97
                have assump_109 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_100 := assump_97 assump_109
                apply False.elim assump_100


variable (p1 p2 p3 p7 p0 p6 p4 : Prop)
theorem file85_5290 : (((((p2 ∧ p4) → (p7 → False)) ∧ ((True → False) ∧ (p2 → False))) → (((p7 ∧ False) ∨ (p3 → False)) → ((p6 ∧ p2) → (False ∨ p6)))) ∨ ((((p1 → False) ∧ (p4 → True)) → False) ∧ (((p7 → p7) → (p0 ∨ p7)) ∧ ((p0 → False) → (p1 ∨ p7))))) := by
  apply Or.inl
  intro assump_22
  intro assump_23
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_23
    case inl assump_31 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        apply False.elim assump_34
    case inr assump_32 =>
      cases assump_22
      case intro assump_41 assump_42 =>
        cases assump_42
        case intro assump_45 assump_46 =>
          apply Or.inr
          exact assump_25


variable (p0 p1 p2 p6 p4 p7 p5 : Prop)
theorem file85_6058 : (((((p1 ∨ p1) → (p4 → False)) ∧ ((p1 → p0) ∨ (p1 ∧ p2))) ∧ (((p7 → False) ∨ (p1 → p6)) ∧ ((False → False) ∧ (False ∧ p7)))) → ((((p1 → False) → False) → False) ∧ (((p5 → False) ∨ (True ∨ p5)) → ((p7 → True) ∨ (p5 ∨ True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_16
            case intro assump_21 assump_22 =>
              cases assump_22
              case intro assump_25 assump_26 =>
                apply False.elim assump_25
          case inr assump_18 =>
            cases assump_16
            case intro assump_31 assump_32 =>
              cases assump_32
              case intro assump_35 assump_36 =>
                apply False.elim assump_35
      case inr assump_12 =>
        cases assump_12
        case intro assump_39 assump_40 =>
          cases assump_6
          case intro assump_45 assump_46 =>
            cases assump_45
            case inl assump_47 =>
              cases assump_46
              case intro assump_51 assump_52 =>
                cases assump_52
                case intro assump_55 assump_56 =>
                  apply False.elim assump_55
            case inr assump_48 =>
              cases assump_46
              case intro assump_61 assump_62 =>
                cases assump_62
                case intro assump_65 assump_66 =>
                  apply False.elim assump_65
  intro assump_69
  cases assump_69
  case inl assump_70 =>
    cases assump_1
    case intro assump_74 assump_75 =>
      cases assump_74
      case intro assump_76 assump_77 =>
        cases assump_77
        case inl assump_80 =>
          cases assump_75
          case intro assump_84 assump_85 =>
            cases assump_84
            case inl assump_86 =>
              cases assump_85
              case intro assump_90 assump_91 =>
                cases assump_91
                case intro assump_94 assump_95 =>
                  apply False.elim assump_94
            case inr assump_87 =>
              cases assump_85
              case intro assump_100 assump_101 =>
                cases assump_101
                case intro assump_104 assump_105 =>
                  apply False.elim assump_104
        case inr assump_81 =>
          cases assump_81
          case intro assump_108 assump_109 =>
            cases assump_75
            case intro assump_114 assump_115 =>
              cases assump_114
              case inl assump_116 =>
                cases assump_115
                case intro assump_120 assump_121 =>
                  cases assump_121
                  case intro assump_124 assump_125 =>
                    apply False.elim assump_124
              case inr assump_117 =>
                cases assump_115
                case intro assump_130 assump_131 =>
                  cases assump_131
                  case intro assump_134 assump_135 =>
                    apply False.elim assump_134
  case inr assump_71 =>
    cases assump_71
    case inl assump_138 =>
      cases assump_1
      case intro assump_142 assump_143 =>
        cases assump_142
        case intro assump_144 assump_145 =>
          cases assump_145
          case inl assump_148 =>
            cases assump_143
            case intro assump_152 assump_153 =>
              cases assump_152
              case inl assump_154 =>
                cases assump_153
                case intro assump_158 assump_159 =>
                  cases assump_159
                  case intro assump_162 assump_163 =>
                    apply False.elim assump_162
              case inr assump_155 =>
                cases assump_153
                case intro assump_168 assump_169 =>
                  cases assump_169
                  case intro assump_172 assump_173 =>
                    apply False.elim assump_172
          case inr assump_149 =>
            cases assump_149
            case intro assump_176 assump_177 =>
              cases assump_143
              case intro assump_182 assump_183 =>
                cases assump_182
                case inl assump_184 =>
                  cases assump_183
                  case intro assump_188 assump_189 =>
                    cases assump_189
                    case intro assump_192 assump_193 =>
                      apply False.elim assump_192
                case inr assump_185 =>
                  cases assump_183
                  case intro assump_198 assump_199 =>
                    cases assump_199
                    case intro assump_202 assump_203 =>
                      apply False.elim assump_202
    case inr assump_139 =>
      cases assump_1
      case intro assump_208 assump_209 =>
        cases assump_208
        case intro assump_210 assump_211 =>
          cases assump_211
          case inl assump_214 =>
            cases assump_209
            case intro assump_218 assump_219 =>
              cases assump_218
              case inl assump_220 =>
                cases assump_219
                case intro assump_224 assump_225 =>
                  cases assump_225
                  case intro assump_228 assump_229 =>
                    apply False.elim assump_228
              case inr assump_221 =>
                cases assump_219
                case intro assump_234 assump_235 =>
                  cases assump_235
                  case intro assump_238 assump_239 =>
                    apply False.elim assump_238
          case inr assump_215 =>
            cases assump_215
            case intro assump_242 assump_243 =>
              cases assump_209
              case intro assump_248 assump_249 =>
                cases assump_248
                case inl assump_250 =>
                  cases assump_249
                  case intro assump_254 assump_255 =>
                    cases assump_255
                    case intro assump_258 assump_259 =>
                      apply False.elim assump_258
                case inr assump_251 =>
                  cases assump_249
                  case intro assump_264 assump_265 =>
                    cases assump_265
                    case intro assump_268 assump_269 =>
                      apply False.elim assump_268


variable (p7 p4 : Prop)
theorem file85_12566 : (((((p7 → p7) ∨ (p7 → False)) → False) ∧ (((p4 ∧ True) ∨ (False → p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((p4 ∧ True) ∨ (False → p7)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p6 p7 p4 p3 : Prop)
theorem file85_12984 : ((((((p4 ∧ p7) ∧ (False ∨ p7)) ∧ ((p3 → False) → (p6 → False))) → False) ∧ ((((True → p1) → (p6 ∧ p3)) → False) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_23 : ((True → False) → False) := by
        intro assump_13
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_13 assump_24
        apply False.elim assump_16
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12


variable (p5 p2 p0 p3 p6 p1 p7 : Prop)
theorem file85_13632 : ((((((p1 → p6) → False) ∧ ((p6 ∨ p3) ∧ (p3 → p5))) → (((True ∧ p1) ∨ (p5 → False)) → ((p2 ∧ p7) ∨ (p0 → True)))) → False) → False) := by
  intro assump_1
  have assump_56 : ((((p1 → p6) → False) ∧ ((p6 ∨ p3) ∧ (p3 → p5))) → (((True ∧ p1) ∨ (p5 → False)) → ((p2 ∧ p7) ∨ (p0 → True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              apply Or.inr
              intro assump_27
              apply True.intro
            case inr assump_22 =>
              apply Or.inr
              intro assump_32
              apply True.intro
    case inr assump_8 =>
      cases assump_5
      case intro assump_35 assump_36 =>
        cases assump_36
        case intro assump_39 assump_40 =>
          cases assump_39
          case inl assump_41 =>
            apply Or.inr
            intro assump_47
            apply True.intro
          case inr assump_42 =>
            apply Or.inr
            intro assump_52
            apply True.intro
  let assump_4 := assump_1 assump_56
  apply False.elim assump_4


variable (p5 p2 p6 p7 p0 p4 p1 : Prop)
theorem file85_15005 : (((((False → p2) → False) → ((p7 ∧ p0) ∧ (p5 ∨ p6))) ∨ (((p1 → p0) → False) ∨ ((True → p7) ∨ (p5 ∧ p2)))) ∨ ((((False ∧ p4) ∨ (p6 → p4)) ∧ ((p5 → False) ∨ (p7 → p5))) → (((p7 ∨ p6) → False) → ((p4 ∨ p5) ∨ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_29 : (False → p2) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4
  have assump_30 : (False → p2) := by
    intro assump_14
    apply False.elim assump_14
  let assump_13 := assump_1 assump_30
  apply False.elim assump_13
  have assump_31 : (False → p2) := by
    intro assump_23
    apply False.elim assump_23
  let assump_22 := assump_1 assump_31
  apply False.elim assump_22


variable (p3 p5 : Prop)
theorem file85_15828 : ((((((p5 ∨ p5) ∨ (p3 ∧ False)) ∧ ((p5 → p5) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p5 ∨ p5) ∨ (p3 ∧ False)) ∧ ((p5 → p5) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_44 : (p5 → p5) := by
            intro assump_17
            exact assump_17
          let assump_16 := assump_7 assump_44
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_45 : (p5 → p5) := by
            intro assump_28
            exact assump_28
          let assump_27 := assump_7 assump_45
          apply False.elim assump_27
      case inr assump_9 =>
        cases assump_9
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p4 p7 p5 p0 p3 p1 p2 : Prop)
theorem file85_16844 : ((((((p4 ∨ p3) ∨ (p3 ∨ False)) ∨ ((p2 ∨ p7) ∧ (p0 → p5))) → (((p7 ∨ p0) → (p5 → p5)) ∨ ((p1 → False) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_87 : ((((p4 ∨ p3) ∨ (p3 ∨ False)) ∨ ((p2 ∨ p7) ∧ (p0 → p5))) → (((p7 ∨ p0) → (p5 → p5)) ∨ ((p1 → False) → (p1 → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          intro assump_14
          intro assump_15
          cases assump_14
          case inl assump_18 =>
            exact assump_15
          case inr assump_19 =>
            exact assump_15
        case inr assump_11 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          cases assump_26
          case inl assump_30 =>
            exact assump_27
          case inr assump_31 =>
            exact assump_27
      case inr assump_9 =>
        cases assump_9
        case inl assump_36 =>
          apply Or.inl
          intro assump_40
          intro assump_41
          cases assump_40
          case inl assump_44 =>
            exact assump_41
          case inr assump_45 =>
            exact assump_41
        case inr assump_37 =>
          apply False.elim assump_37
    case inr assump_7 =>
      cases assump_7
      case intro assump_52 assump_53 =>
        cases assump_52
        case inl assump_54 =>
          apply Or.inl
          intro assump_60
          intro assump_61
          cases assump_60
          case inl assump_64 =>
            exact assump_61
          case inr assump_65 =>
            exact assump_61
        case inr assump_55 =>
          apply Or.inl
          intro assump_74
          intro assump_75
          cases assump_74
          case inl assump_78 =>
            exact assump_75
          case inr assump_79 =>
            exact assump_75
  let assump_4 := assump_1 assump_87
  apply False.elim assump_4


variable (p3 p5 p6 p2 p0 : Prop)
theorem file85_18884 : ((((((p6 → False) ∧ (p3 → False)) → ((p3 ∧ p5) → False)) ∨ (((False ∧ False) → False) ∨ ((p2 → False) ∧ (p0 → p2)))) → False) → False) := by
  intro assump_5
  have assump_30 : ((((p6 → False) ∧ (p3 → False)) → ((p3 ∧ p5) → False)) ∨ (((False ∧ False) → False) ∨ ((p2 → False) ∧ (p0 → p2)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_9
      case intro assump_17 assump_18 =>
        have assump_31 : p3 := by
          exact assump_11
        let assump_23 := assump_18 assump_31
        apply False.elim assump_23
  let assump_8 := assump_5 assump_30
  apply False.elim assump_8


variable (p6 p7 p2 p0 p4 p1 p5 p3 : Prop)
theorem file85_19628 : ((((((p4 ∨ False) ∨ (p6 → False)) → False) ∧ (((p1 ∧ p7) → (p4 → p1)) → False)) ∧ ((((True ∨ p5) ∧ (p0 → p0)) ∧ ((True ∧ p5) → False)) ∧ (((True → p0) ∧ (p3 → p1)) ∧ ((p2 → False) ∧ (p6 ∧ p7))))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_21
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              cases assump_29
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  cases assump_43
                  case intro assump_50 assump_51 =>
                    cases assump_51
                    case intro assump_54 assump_55 =>
                      have assump_116 : ((p1 ∧ p7) → (p4 → p1)) := by
                        intro assump_69
                        intro assump_70
                        cases assump_69
                        case intro assump_73 assump_74 =>
                          exact assump_73
                      let assump_68 := assump_23 assump_116
                      apply False.elim assump_68
            case inr assump_35 =>
              cases assump_29
              case intro assump_88 assump_89 =>
                cases assump_88
                case intro assump_90 assump_91 =>
                  cases assump_89
                  case intro assump_96 assump_97 =>
                    cases assump_97
                    case intro assump_100 assump_101 =>
                      have assump_117 : (True ∧ p5) := by
                        apply And.intro
                        apply True.intro
                        exact assump_35
                      let assump_112 := assump_31 assump_117
                      apply False.elim assump_112


variable (p5 p7 p3 p0 p6 p2 : Prop)
theorem file85_21686 : ((((((p7 ∨ p6) ∧ (False ∧ p2)) ∧ ((p5 → False) ∨ (p6 → False))) → (((p3 → True) ∧ (p6 ∨ p0)) → False)) → False) → False) := by
  intro assump_12
  have assump_67 : ((((p7 ∨ p6) ∧ (False ∧ p2)) ∧ ((p5 → False) ∨ (p6 → False))) → (((p3 → True) ∧ (p6 ∨ p0)) → False)) := by
    intro assump_16
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_19
      case inl assump_22 =>
        cases assump_16
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_28
            case inl assump_30 =>
              cases assump_29
              case intro assump_34 assump_35 =>
                apply False.elim assump_34
            case inr assump_31 =>
              cases assump_29
              case intro assump_40 assump_41 =>
                apply False.elim assump_40
      case inr assump_23 =>
        cases assump_16
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_48
            case inl assump_50 =>
              cases assump_49
              case intro assump_54 assump_55 =>
                apply False.elim assump_54
            case inr assump_51 =>
              cases assump_49
              case intro assump_60 assump_61 =>
                apply False.elim assump_60
  let assump_15 := assump_12 assump_67
  apply False.elim assump_15


variable (p6 p3 p1 p7 p2 : Prop)
theorem file85_23206 : ((((((False → False) ∨ (p7 ∧ p1)) → False) → (((p1 → False) ∧ (p7 → p2)) ∧ ((p6 → False) ∧ (p3 → False)))) → False) → False) := by
  intro assump_9
  have assump_65 : ((((False → False) ∨ (p7 ∧ p1)) → False) → (((p1 → False) ∧ (p7 → p2)) ∧ ((p6 → False) ∧ (p3 → False)))) := by
    intro assump_13
    apply And.intro
    apply And.intro
    intro assump_14
    have assump_66 : ((False → False) ∨ (p7 ∧ p1)) := by
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_13 assump_66
    apply False.elim assump_19
    intro assump_26
    have assump_67 : ((False → False) ∨ (p7 ∧ p1)) := by
      apply Or.inl
      intro assump_32
      apply False.elim assump_32
    let assump_31 := assump_13 assump_67
    apply False.elim assump_31
    apply And.intro
    intro assump_38
    have assump_68 : ((False → False) ∨ (p7 ∧ p1)) := by
      apply Or.inl
      intro assump_44
      apply False.elim assump_44
    let assump_43 := assump_13 assump_68
    apply False.elim assump_43
    intro assump_50
    have assump_69 : ((False → False) ∨ (p7 ∧ p1)) := by
      apply Or.inl
      intro assump_56
      apply False.elim assump_56
    let assump_55 := assump_13 assump_69
    apply False.elim assump_55
  let assump_12 := assump_9 assump_65
  apply False.elim assump_12


variable (p2 p0 p5 p4 p3 p6 : Prop)
theorem file85_24583 : ((((((p0 → p0) ∧ (p6 → False)) → ((False ∨ p5) → False)) ∧ (((p2 → p0) ∧ (p2 → True)) → ((p6 ∧ p4) ∨ (False → False)))) ∧ ((((False → False) → False) → ((p5 → False) → (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_32 : (((False → False) → False) → ((p5 → False) → (p3 → False))) := by
        intro assump_13
        intro assump_14
        intro assump_15
        have assump_33 : (False → False) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_13 assump_33
        apply False.elim assump_22
      let assump_12 := assump_3 assump_32
      apply False.elim assump_12


variable (p3 p6 p2 p0 p1 p7 p4 : Prop)
theorem file85_25403 : ((((((p6 → True) → (p2 → p1)) ∨ ((True → False) ∧ (p7 → False))) → (((p6 → False) → (p2 → False)) → ((p2 → False) ∧ (True → False)))) ∧ ((((p4 ∨ p6) ∧ (p1 → p1)) → ((True → False) → (p0 → p3))) → (((False → False) → (p1 → True)) → False))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_56 : (((p4 ∨ p6) ∧ (p1 → p1)) → ((True → False) → (p0 → p3))) := by
      intro assump_19
      intro assump_20
      intro assump_21
      cases assump_19
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          have assump_57 : True := by
            apply True.intro
          let assump_36 := assump_20 assump_57
          apply False.elim assump_36
        case inr assump_29 =>
          have assump_58 : True := by
            apply True.intro
          let assump_46 := assump_20 assump_58
          apply False.elim assump_46
    let assump_18 := assump_13 assump_56
    have assump_59 : ((False → False) → (p1 → True)) := by
      intro assump_51
      intro assump_52
      apply True.intro
    let assump_50 := assump_18 assump_59
    apply False.elim assump_50


variable (p6 p4 p5 p2 p3 p0 : Prop)
theorem file85_26627 : (((((p4 ∨ p3) ∧ (True → False)) ∧ ((p5 ∨ p0) ∨ (True → p2))) → False) ∨ ((((p3 → False) ∨ (False → False)) ∨ ((p0 ∨ p6) → (False ∧ True))) → (((True → False) → False) → False))) := by
  apply Or.inl
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
            have assump_68 : True := by
              apply True.intro
            let assump_19 := assump_5 assump_68
            apply False.elim assump_19
          case inr assump_15 =>
            have assump_69 : True := by
              apply True.intro
            let assump_26 := assump_5 assump_69
            apply False.elim assump_26
        case inr assump_13 =>
          have assump_70 : True := by
            apply True.intro
          let assump_34 := assump_5 assump_70
          apply False.elim assump_34
      case inr assump_7 =>
        cases assump_3
        case inl assump_42 =>
          cases assump_42
          case inl assump_44 =>
            have assump_71 : True := by
              apply True.intro
            let assump_49 := assump_5 assump_71
            apply False.elim assump_49
          case inr assump_45 =>
            have assump_72 : True := by
              apply True.intro
            let assump_56 := assump_5 assump_72
            apply False.elim assump_56
        case inr assump_43 =>
          have assump_73 : True := by
            apply True.intro
          let assump_64 := assump_5 assump_73
          apply False.elim assump_64


variable (p5 p7 p6 p3 p2 p1 p4 : Prop)
theorem file85_28365 : (((((p6 ∨ p5) ∧ (p2 ∨ p2)) ∨ ((p3 ∧ True) ∧ (p1 → False))) → (((p4 → p1) ∧ (True → False)) → False)) ∨ ((((p6 → True) → False) ∨ ((p2 ∨ True) → False)) ∨ (((p4 ∨ True) ∧ (p3 → False)) ∧ ((p7 → p2) → (p6 → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            have assump_71 : True := by
              apply True.intro
            let assump_23 := assump_4 assump_71
            apply False.elim assump_23
          case inr assump_18 =>
            have assump_72 : True := by
              apply True.intro
            let assump_31 := assump_4 assump_72
            apply False.elim assump_31
        case inr assump_14 =>
          cases assump_12
          case inl assump_37 =>
            have assump_73 : True := by
              apply True.intro
            let assump_43 := assump_4 assump_73
            apply False.elim assump_43
          case inr assump_38 =>
            have assump_74 : True := by
              apply True.intro
            let assump_51 := assump_4 assump_74
            apply False.elim assump_51
    case inr assump_10 =>
      cases assump_10
      case intro assump_55 assump_56 =>
        cases assump_55
        case intro assump_57 assump_58 =>
          have assump_75 : True := by
            apply True.intro
          let assump_67 := assump_4 assump_75
          apply False.elim assump_67


variable (p2 : Prop)
theorem file85_30034 : ((((((False → False) ∨ (p2 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∨ (p2 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∨ (p2 → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p2 p3 p0 p4 p7 p6 p5 : Prop)
theorem file85_30559 : ((((((p1 ∨ p2) ∧ (p5 → p5)) ∧ ((True → False) ∧ (p3 ∧ p6))) ∨ (((True → False) ∨ (p4 ∨ True)) ∨ ((p7 → False) ∨ (p6 ∧ p7)))) ∧ ((((p6 ∨ p5) ∧ (p6 ∧ p0)) → False) ∧ (((p6 ∨ p3) ∧ (p5 → p2)) ∧ ((p4 → p3) ∧ (p0 ∧ p6))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_11
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_7
                case intro assump_30 assump_31 =>
                  cases assump_31
                  case intro assump_34 assump_35 =>
                    cases assump_34
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case inl assump_38 =>
                        cases assump_35
                        case intro assump_44 assump_45 =>
                          cases assump_45
                          case intro assump_48 assump_49 =>
                            have assump_460 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                              apply And.intro
                              apply Or.inl
                              exact assump_49
                              apply And.intro
                              exact assump_49
                              exact assump_48
                            let assump_59 := assump_30 assump_460
                            apply False.elim assump_59
                      case inr assump_39 =>
                        cases assump_35
                        case intro assump_67 assump_68 =>
                          cases assump_68
                          case intro assump_71 assump_72 =>
                            have assump_461 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                              apply And.intro
                              apply Or.inl
                              exact assump_72
                              apply And.intro
                              exact assump_72
                              exact assump_71
                            let assump_82 := assump_30 assump_461
                            apply False.elim assump_82
          case inr assump_15 =>
            cases assump_11
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                cases assump_7
                case intro assump_100 assump_101 =>
                  cases assump_101
                  case intro assump_104 assump_105 =>
                    cases assump_104
                    case intro assump_106 assump_107 =>
                      cases assump_106
                      case inl assump_108 =>
                        cases assump_105
                        case intro assump_114 assump_115 =>
                          cases assump_115
                          case intro assump_118 assump_119 =>
                            have assump_462 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                              apply And.intro
                              apply Or.inl
                              exact assump_119
                              apply And.intro
                              exact assump_119
                              exact assump_118
                            let assump_129 := assump_100 assump_462
                            apply False.elim assump_129
                      case inr assump_109 =>
                        cases assump_105
                        case intro assump_137 assump_138 =>
                          cases assump_138
                          case intro assump_141 assump_142 =>
                            have assump_463 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                              apply And.intro
                              apply Or.inl
                              exact assump_142
                              apply And.intro
                              exact assump_142
                              exact assump_141
                            let assump_152 := assump_100 assump_463
                            apply False.elim assump_152
    case inr assump_9 =>
      cases assump_9
      case inl assump_156 =>
        cases assump_156
        case inl assump_158 =>
          cases assump_7
          case intro assump_162 assump_163 =>
            cases assump_163
            case intro assump_166 assump_167 =>
              cases assump_166
              case intro assump_168 assump_169 =>
                cases assump_168
                case inl assump_170 =>
                  cases assump_167
                  case intro assump_176 assump_177 =>
                    cases assump_177
                    case intro assump_180 assump_181 =>
                      have assump_464 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_181
                        apply And.intro
                        exact assump_181
                        exact assump_180
                      let assump_191 := assump_162 assump_464
                      apply False.elim assump_191
                case inr assump_171 =>
                  cases assump_167
                  case intro assump_199 assump_200 =>
                    cases assump_200
                    case intro assump_203 assump_204 =>
                      have assump_465 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_204
                        apply And.intro
                        exact assump_204
                        exact assump_203
                      let assump_214 := assump_162 assump_465
                      apply False.elim assump_214
        case inr assump_159 =>
          cases assump_159
          case inl assump_218 =>
            cases assump_7
            case intro assump_222 assump_223 =>
              cases assump_223
              case intro assump_226 assump_227 =>
                cases assump_226
                case intro assump_228 assump_229 =>
                  cases assump_228
                  case inl assump_230 =>
                    cases assump_227
                    case intro assump_236 assump_237 =>
                      cases assump_237
                      case intro assump_240 assump_241 =>
                        have assump_466 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_241
                          apply And.intro
                          exact assump_241
                          exact assump_240
                        let assump_252 := assump_222 assump_466
                        apply False.elim assump_252
                  case inr assump_231 =>
                    cases assump_227
                    case intro assump_260 assump_261 =>
                      cases assump_261
                      case intro assump_264 assump_265 =>
                        have assump_467 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_265
                          apply And.intro
                          exact assump_265
                          exact assump_264
                        let assump_276 := assump_222 assump_467
                        apply False.elim assump_276
          case inr assump_219 =>
            cases assump_7
            case intro assump_282 assump_283 =>
              cases assump_283
              case intro assump_286 assump_287 =>
                cases assump_286
                case intro assump_288 assump_289 =>
                  cases assump_288
                  case inl assump_290 =>
                    cases assump_287
                    case intro assump_296 assump_297 =>
                      cases assump_297
                      case intro assump_300 assump_301 =>
                        have assump_468 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_301
                          apply And.intro
                          exact assump_301
                          exact assump_300
                        let assump_311 := assump_282 assump_468
                        apply False.elim assump_311
                  case inr assump_291 =>
                    cases assump_287
                    case intro assump_319 assump_320 =>
                      cases assump_320
                      case intro assump_323 assump_324 =>
                        have assump_469 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_324
                          apply And.intro
                          exact assump_324
                          exact assump_323
                        let assump_334 := assump_282 assump_469
                        apply False.elim assump_334
      case inr assump_157 =>
        cases assump_157
        case inl assump_338 =>
          cases assump_7
          case intro assump_342 assump_343 =>
            cases assump_343
            case intro assump_346 assump_347 =>
              cases assump_346
              case intro assump_348 assump_349 =>
                cases assump_348
                case inl assump_350 =>
                  cases assump_347
                  case intro assump_356 assump_357 =>
                    cases assump_357
                    case intro assump_360 assump_361 =>
                      have assump_470 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_361
                        apply And.intro
                        exact assump_361
                        exact assump_360
                      let assump_371 := assump_342 assump_470
                      apply False.elim assump_371
                case inr assump_351 =>
                  cases assump_347
                  case intro assump_379 assump_380 =>
                    cases assump_380
                    case intro assump_383 assump_384 =>
                      have assump_471 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                        apply And.intro
                        apply Or.inl
                        exact assump_384
                        apply And.intro
                        exact assump_384
                        exact assump_383
                      let assump_394 := assump_342 assump_471
                      apply False.elim assump_394
        case inr assump_339 =>
          cases assump_339
          case intro assump_398 assump_399 =>
            cases assump_7
            case intro assump_404 assump_405 =>
              cases assump_405
              case intro assump_408 assump_409 =>
                cases assump_408
                case intro assump_410 assump_411 =>
                  cases assump_410
                  case inl assump_412 =>
                    cases assump_409
                    case intro assump_418 assump_419 =>
                      cases assump_419
                      case intro assump_422 assump_423 =>
                        have assump_472 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_423
                          apply And.intro
                          exact assump_423
                          exact assump_422
                        let assump_433 := assump_404 assump_472
                        apply False.elim assump_433
                  case inr assump_413 =>
                    cases assump_409
                    case intro assump_441 assump_442 =>
                      cases assump_442
                      case intro assump_445 assump_446 =>
                        have assump_473 : ((p6 ∨ p5) ∧ (p6 ∧ p0)) := by
                          apply And.intro
                          apply Or.inl
                          exact assump_446
                          apply And.intro
                          exact assump_446
                          exact assump_445
                        let assump_456 := assump_404 assump_473
                        apply False.elim assump_456


variable (p0 p5 p7 : Prop)
theorem file85_43351 : (((((False ∧ p0) → (p7 → False)) ∨ ((True → p5) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p0) → (p7 → False)) ∨ ((True → p5) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p1 p4 p5 p6 p3 : Prop)
theorem file85_43799 : (((((p4 ∧ p5) → (p4 ∧ True)) ∨ ((p3 ∨ p1) ∨ (True → False))) ∨ (((p0 ∨ False) ∧ (True → False)) → False)) ∨ ((((False ∨ p1) ∧ (p6 → p4)) → False) ∨ (((True → False) ∧ (True ∧ p3)) ∧ ((False → p3) ∨ (p4 ∨ True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    exact assump_2
  apply True.intro


variable (p0 : Prop)
theorem file85_44233 : (((((p0 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p0 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p0 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p1 p0 p3 p6 p7 p2 p4 : Prop)
theorem file85_44667 : ((((((p2 → False) ∨ (p4 ∧ p1)) ∧ ((False ∧ p1) → (p6 → p1))) → (((p2 ∨ p2) → False) → False)) ∧ ((((p7 → False) ∧ (p0 → p3)) ∨ ((p3 ∨ p7) → (True → p1))) ∧ (((p5 → True) → False) ∧ ((p7 ∧ p3) → (p4 ∧ p7))))) → False) := by
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
            have assump_42 : (p5 → True) := by
              intro assump_24
              apply True.intro
            let assump_23 := assump_16 assump_42
            apply False.elim assump_23
      case inr assump_9 =>
        cases assump_7
        case intro assump_30 assump_31 =>
          have assump_43 : (p5 → True) := by
            intro assump_38
            apply True.intro
          let assump_37 := assump_30 assump_43
          apply False.elim assump_37


variable (p5 p3 p6 p4 p1 : Prop)
theorem file85_45726 : (((((p3 → False) → (True → True)) ∧ ((p4 ∧ p4) → (p5 → False))) → False) → ((((p6 → False) ∧ (True → False)) → False) ∨ (((p5 → True) → (p6 ∨ True)) ∧ ((False → p4) ∨ (False ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_15 : True := by
      apply True.intro
    let assump_11 := assump_6 assump_15
    apply False.elim assump_11


variable (p4 p2 p1 p3 : Prop)
theorem file85_46196 : ((((((False → True) → False) ∧ ((p4 ∨ p2) ∨ (p2 → False))) → (((p1 ∨ p3) → False) → ((False ∧ p2) → False))) → False) → False) := by
  intro assump_10
  have assump_24 : ((((False → True) → False) ∧ ((p4 ∨ p2) ∨ (p2 → False))) → (((p1 ∨ p3) → False) → ((False ∧ p2) → False))) := by
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  let assump_13 := assump_10 assump_24
  apply False.elim assump_13


variable (p4 p5 p6 p2 : Prop)
theorem file85_46752 : (((((p2 ∧ True) ∧ (p6 → False)) → ((False ∧ False) → (p4 → p5))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p2 ∧ True) ∧ (p6 → False)) → ((False ∧ False) → (p4 → p5))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p7 p1 p0 p3 p2 p5 p6 : Prop)
theorem file85_47224 : (((((True → False) → False) ∧ ((p7 ∧ p2) → (False → False))) ∨ (((p5 ∧ p4) ∧ (p5 ∧ p4)) ∨ ((p2 ∨ p3) ∧ (p6 → p6)))) ∨ ((((p2 ∨ p3) → False) → ((p2 → p2) ∧ (p3 ∧ p5))) → (((False ∨ p1) → (p6 → p4)) ∨ ((True ∨ p0) ∧ (p2 ∧ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_12 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4
  intro assump_8
  intro assump_9
  apply False.elim assump_9


variable (p6 p1 p5 p2 p0 p7 : Prop)
theorem file85_47761 : (((((p1 ∧ p6) ∨ (p2 ∧ p1)) ∧ ((p6 → False) → (p5 → p5))) → False) → ((((p7 ∨ p0) ∨ (p2 → p6)) → ((p5 → False) → False)) → (((p1 → False) → (p1 → False)) ∨ ((p0 → True) → False)))) := by
  intro assump_5
  intro assump_6
  apply Or.inl
  intro assump_11
  intro assump_12
  have assump_21 : p1 := by
    exact assump_12
  let assump_17 := assump_11 assump_21
  apply False.elim assump_17


variable (p4 p2 p3 p0 : Prop)
theorem file85_48202 : (((((False ∧ p3) → (p0 ∧ p3)) ∨ ((p0 ∧ True) → False)) ∨ (((p3 ∨ p4) ∧ (p2 → False)) ∨ ((p2 → False) ∧ (p2 → False)))) ∨ ((((False → False) ∨ (p4 → False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  cases assump_1
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p2 p5 p1 p6 p7 : Prop)
theorem file85_48682 : (((((p2 → False) → False) → False) → False) → ((((p6 ∨ p7) ∨ (p2 ∧ p6)) ∨ ((False ∧ p6) → (p5 → False))) ∨ (((p7 → False) ∧ (p5 → p1)) ∧ ((p5 ∧ p6) → (p7 → True))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p3 p5 p1 p2 p7 p6 p4 p0 : Prop)
theorem file85_49082 : (((((p4 ∧ p1) ∨ (p2 ∨ True)) → ((p4 ∧ p5) → False)) ∧ (((p3 → True) → False) ∧ ((p0 → p2) ∧ (p6 ∧ p0)))) → ((((False → p0) → (p7 → p3)) ∧ ((p0 ∨ p6) → False)) ∧ (((p7 ∧ p2) → (p3 → False)) ∨ ((False ∧ p6) → (p3 ∨ p6))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          have assump_136 : (p3 → True) := by
            intro assump_31
            apply True.intro
          let assump_30 := assump_12 assump_136
          apply False.elim assump_30
  intro assump_35
  cases assump_35
  case inl assump_36 =>
    cases assump_1
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        cases assump_45
        case intro assump_48 assump_49 =>
          cases assump_49
          case intro assump_52 assump_53 =>
            have assump_137 : (p3 → True) := by
              intro assump_63
              apply True.intro
            let assump_62 := assump_44 assump_137
            apply False.elim assump_62
  case inr assump_37 =>
    cases assump_1
    case intro assump_69 assump_70 =>
      cases assump_70
      case intro assump_73 assump_74 =>
        cases assump_74
        case intro assump_77 assump_78 =>
          cases assump_78
          case intro assump_81 assump_82 =>
            have assump_138 : (p3 → True) := by
              intro assump_92
              apply True.intro
            let assump_91 := assump_73 assump_138
            apply False.elim assump_91
  cases assump_1
  case intro assump_96 assump_97 =>
    cases assump_97
    case intro assump_100 assump_101 =>
      cases assump_101
      case intro assump_104 assump_105 =>
        cases assump_105
        case intro assump_108 assump_109 =>
          apply Or.inl
          intro assump_114
          intro assump_115
          cases assump_114
          case intro assump_118 assump_119 =>
            have assump_139 : (p3 → True) := by
              intro assump_132
              apply True.intro
            let assump_131 := assump_100 assump_139
            apply False.elim assump_131


variable (p1 p0 p5 p6 p2 p3 p4 p7 : Prop)
theorem file85_51475 : (((((p4 ∧ p0) ∨ (p5 ∨ p5)) → False) ∧ (((False ∧ p2) → (p5 ∨ p5)) → ((False ∧ p3) ∨ (False ∧ p0)))) → ((((False ∧ p6) → False) ∧ ((p1 ∧ p2) ∧ (p7 ∨ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          cases assump_1
          case intro assump_19 assump_20 =>
            have assump_44 : ((False ∧ p2) → (p5 ∨ p5)) := by
              intro assump_26
              cases assump_26
              case intro assump_27 assump_28 =>
                apply False.elim assump_27
            let assump_25 := assump_20 assump_44
            cases assump_25
            case inl assump_32 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                apply False.elim assump_34
            case inr assump_33 =>
              cases assump_33
              case intro assump_38 assump_39 =>
                apply False.elim assump_38
        case inr assump_16 =>
          apply False.elim assump_16


variable (p0 p2 p3 p6 p5 p1 : Prop)
theorem file85_52697 : (((((False → False) ∨ (p1 → False)) → False) → False) ∨ ((((False ∨ p3) → (p0 → False)) ∨ ((p0 ∧ False) ∧ (p6 ∧ True))) ∨ (((p3 → p2) ∧ (p0 → p5)) ∨ ((p0 ∨ False) ∧ (True ∨ False))))) := by
  apply Or.inl
  intro assump_20
  have assump_30 : ((False → False) ∨ (p1 → False)) := by
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
  let assump_23 := assump_20 assump_30
  apply False.elim assump_23


variable (p7 p4 : Prop)
theorem file85_53162 : ((((((p4 → p4) ∨ (p7 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 → p4) ∨ (p7 → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p4 → p4) ∨ (p7 → False)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p2 p0 p1 p6 p5 : Prop)
theorem file85_53652 : (((((p0 → p1) → False) ∧ ((p6 ∨ p4) ∧ (p6 → p2))) → (((p5 ∧ p1) → False) → ((p4 → False) → False))) → ((((p1 → False) → False) → False) → (((p4 → p0) ∨ (False ∧ True)) → ((True ∨ p0) ∨ (p0 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_5 =>
    cases assump_5
    case intro assump_12 assump_13 =>
      apply False.elim assump_12


variable (p7 p6 p4 p3 p1 p0 : Prop)
theorem file85_54176 : (((((p0 ∨ p7) ∧ (p1 → False)) ∧ ((p7 → False) ∨ (p0 ∧ p0))) ∧ (((p3 → False) → (p6 → False)) → ((p6 ∧ p7) ∧ (p3 ∧ p4)))) → ((((False ∨ p7) ∨ (p7 ∧ p6)) → ((p1 → False) → (p7 ∨ p0))) ∨ (((p4 → p6) ∨ (p4 → False)) ∨ ((p0 ∨ True) ∨ (p6 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case inl assump_14 =>
            apply Or.inl
            intro assump_20
            intro assump_21
            cases assump_20
            case inl assump_24 =>
              cases assump_24
              case inl assump_26 =>
                apply False.elim assump_26
              case inr assump_27 =>
                apply Or.inl
                exact assump_27
            case inr assump_25 =>
              cases assump_25
              case intro assump_32 assump_33 =>
                apply Or.inl
                exact assump_32
          case inr assump_15 =>
            cases assump_15
            case intro assump_38 assump_39 =>
              apply Or.inl
              intro assump_46
              intro assump_47
              cases assump_46
              case inl assump_50 =>
                cases assump_50
                case inl assump_52 =>
                  apply False.elim assump_52
                case inr assump_53 =>
                  apply Or.inl
                  exact assump_53
              case inr assump_51 =>
                cases assump_51
                case intro assump_58 assump_59 =>
                  apply Or.inl
                  exact assump_58
        case inr assump_9 =>
          cases assump_5
          case inl assump_68 =>
            apply Or.inl
            intro assump_74
            intro assump_75
            cases assump_74
            case inl assump_78 =>
              cases assump_78
              case inl assump_80 =>
                apply False.elim assump_80
              case inr assump_81 =>
                apply Or.inl
                exact assump_81
            case inr assump_79 =>
              cases assump_79
              case intro assump_86 assump_87 =>
                apply Or.inl
                exact assump_86
          case inr assump_69 =>
            cases assump_69
            case intro assump_92 assump_93 =>
              apply Or.inl
              intro assump_100
              intro assump_101
              cases assump_100
              case inl assump_104 =>
                cases assump_104
                case inl assump_106 =>
                  apply False.elim assump_106
                case inr assump_107 =>
                  apply Or.inl
                  exact assump_107
              case inr assump_105 =>
                cases assump_105
                case intro assump_112 assump_113 =>
                  apply Or.inl
                  exact assump_112


variable (p4 p2 : Prop)
theorem file85_57231 : (((((True → p2) → False) → ((p4 ∧ p2) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → p2) → False) → ((p4 ∧ p2) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_26 : (True → p2) := by
        intro assump_16
        exact assump_8
      let assump_15 := assump_5 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p7 p0 p3 p1 p6 p2 : Prop)
theorem file85_57775 : (((((False ∨ p2) → False) → False) ∨ (((p0 → p1) ∨ (True ∨ p3)) ∨ ((p3 → p3) ∨ (p4 → p7)))) → ((((p0 ∧ p7) ∧ (False ∧ p0)) → ((p7 ∨ p2) → False)) ∨ (((True ∨ p3) ∨ (p6 → p2)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_13
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
    case inr assump_9 =>
      cases assump_6
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_27
          case intro assump_34 assump_35 =>
            apply False.elim assump_34
  case inr assump_3 =>
    cases assump_3
    case inl assump_38 =>
      cases assump_38
      case inl assump_40 =>
        apply Or.inl
        intro assump_44
        intro assump_45
        cases assump_45
        case inl assump_46 =>
          cases assump_44
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_51
              case intro assump_58 assump_59 =>
                apply False.elim assump_58
        case inr assump_47 =>
          cases assump_44
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_65
              case intro assump_72 assump_73 =>
                apply False.elim assump_72
      case inr assump_41 =>
        cases assump_41
        case inl assump_76 =>
          apply Or.inl
          intro assump_80
          intro assump_81
          cases assump_81
          case inl assump_82 =>
            cases assump_80
            case intro assump_86 assump_87 =>
              cases assump_86
              case intro assump_88 assump_89 =>
                cases assump_87
                case intro assump_94 assump_95 =>
                  apply False.elim assump_94
          case inr assump_83 =>
            cases assump_80
            case intro assump_100 assump_101 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                cases assump_101
                case intro assump_108 assump_109 =>
                  apply False.elim assump_108
        case inr assump_77 =>
          apply Or.inl
          intro assump_114
          intro assump_115
          cases assump_115
          case inl assump_116 =>
            cases assump_114
            case intro assump_120 assump_121 =>
              cases assump_120
              case intro assump_122 assump_123 =>
                cases assump_121
                case intro assump_128 assump_129 =>
                  apply False.elim assump_128
          case inr assump_117 =>
            cases assump_114
            case intro assump_134 assump_135 =>
              cases assump_134
              case intro assump_136 assump_137 =>
                cases assump_135
                case intro assump_142 assump_143 =>
                  apply False.elim assump_142
    case inr assump_39 =>
      cases assump_39
      case inl assump_146 =>
        apply Or.inl
        intro assump_150
        intro assump_151
        cases assump_151
        case inl assump_152 =>
          cases assump_150
          case intro assump_156 assump_157 =>
            cases assump_156
            case intro assump_158 assump_159 =>
              cases assump_157
              case intro assump_164 assump_165 =>
                apply False.elim assump_164
        case inr assump_153 =>
          cases assump_150
          case intro assump_170 assump_171 =>
            cases assump_170
            case intro assump_172 assump_173 =>
              cases assump_171
              case intro assump_178 assump_179 =>
                apply False.elim assump_178
      case inr assump_147 =>
        apply Or.inl
        intro assump_184
        intro assump_185
        cases assump_185
        case inl assump_186 =>
          cases assump_184
          case intro assump_190 assump_191 =>
            cases assump_190
            case intro assump_192 assump_193 =>
              cases assump_191
              case intro assump_198 assump_199 =>
                apply False.elim assump_198
        case inr assump_187 =>
          cases assump_184
          case intro assump_204 assump_205 =>
            cases assump_204
            case intro assump_206 assump_207 =>
              cases assump_205
              case intro assump_212 assump_213 =>
                apply False.elim assump_212


variable (p5 p1 p2 p0 p4 p6 p3 : Prop)
theorem file85_62598 : (((((p2 ∨ p3) → (p4 ∨ p5)) ∧ ((p4 → p5) → False)) ∧ (((False ∨ True) ∨ (p4 → False)) ∧ ((p2 → p2) → False))) → ((((p0 ∧ p1) → False) ∨ ((p4 → True) → False)) ∧ (((p3 → p0) → (True → p4)) → ((p0 ∨ p0) → (p6 → False))))) := by
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            apply False.elim assump_18
          case inr assump_19 =>
            apply Or.inl
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              have assump_153 : (p2 → p2) := by
                intro assump_36
                exact assump_36
              let assump_35 := assump_15 assump_153
              apply False.elim assump_35
        case inr assump_17 =>
          apply Or.inl
          intro assump_46
          cases assump_46
          case intro assump_47 assump_48 =>
            have assump_154 : (p2 → p2) := by
              intro assump_56
              exact assump_56
            let assump_55 := assump_15 assump_154
            apply False.elim assump_55
  intro assump_62
  intro assump_63
  intro assump_64
  cases assump_63
  case inl assump_67 =>
    cases assump_5
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        cases assump_74
        case intro assump_81 assump_82 =>
          cases assump_81
          case inl assump_83 =>
            cases assump_83
            case inl assump_85 =>
              apply False.elim assump_85
            case inr assump_86 =>
              have assump_155 : (p2 → p2) := by
                intro assump_94
                exact assump_94
              let assump_93 := assump_82 assump_155
              apply False.elim assump_93
          case inr assump_84 =>
            have assump_156 : (p2 → p2) := by
              intro assump_105
              exact assump_105
            let assump_104 := assump_82 assump_156
            apply False.elim assump_104
  case inr assump_68 =>
    cases assump_5
    case intro assump_115 assump_116 =>
      cases assump_115
      case intro assump_117 assump_118 =>
        cases assump_116
        case intro assump_123 assump_124 =>
          cases assump_123
          case inl assump_125 =>
            cases assump_125
            case inl assump_127 =>
              apply False.elim assump_127
            case inr assump_128 =>
              have assump_157 : (p2 → p2) := by
                intro assump_136
                exact assump_136
              let assump_135 := assump_124 assump_157
              apply False.elim assump_135
          case inr assump_126 =>
            have assump_158 : (p2 → p2) := by
              intro assump_147
              exact assump_147
            let assump_146 := assump_124 assump_158
            apply False.elim assump_146


variable (p3 p7 p1 p6 p5 p4 p0 p2 : Prop)
theorem file85_65723 : (((((False ∧ p0) ∧ (p3 ∨ p2)) → ((p3 ∨ p6) ∧ (p6 ∨ True))) ∨ (((p1 ∨ p7) ∨ (p4 ∧ p3)) ∧ ((p7 ∨ p4) → (False ∧ p3)))) → ((((True ∨ p5) → False) ∧ ((True ∨ p3) ∨ (True ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_1
        case inl assump_13 =>
          have assump_166 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_18 := assump_3 assump_166
          apply False.elim assump_18
        case inr assump_14 =>
          cases assump_14
          case intro assump_22 assump_23 =>
            cases assump_22
            case inl assump_24 =>
              cases assump_24
              case inl assump_26 =>
                have assump_167 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_34 := assump_3 assump_167
                apply False.elim assump_34
              case inr assump_27 =>
                have assump_168 : (p7 ∨ p4) := by
                  apply Or.inl
                  exact assump_27
                let assump_42 := assump_23 assump_168
                let assump_43 := And.left assump_42
                apply False.elim assump_43
            case inr assump_25 =>
              cases assump_25
              case intro assump_47 assump_48 =>
                have assump_169 : (p7 ∨ p4) := by
                  apply Or.inr
                  exact assump_47
                let assump_55 := assump_23 assump_169
                let assump_56 := And.left assump_55
                apply False.elim assump_56
      case inr assump_10 =>
        cases assump_1
        case inl assump_62 =>
          have assump_170 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_68 := assump_3 assump_170
          apply False.elim assump_68
        case inr assump_63 =>
          cases assump_63
          case intro assump_72 assump_73 =>
            cases assump_72
            case inl assump_74 =>
              cases assump_74
              case inl assump_76 =>
                have assump_171 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_85 := assump_3 assump_171
                apply False.elim assump_85
              case inr assump_77 =>
                have assump_172 : (p7 ∨ p4) := by
                  apply Or.inl
                  exact assump_77
                let assump_93 := assump_73 assump_172
                let assump_94 := And.left assump_93
                apply False.elim assump_94
            case inr assump_75 =>
              cases assump_75
              case intro assump_98 assump_99 =>
                have assump_173 : (p7 ∨ p4) := by
                  apply Or.inr
                  exact assump_98
                let assump_106 := assump_73 assump_173
                let assump_107 := And.left assump_106
                apply False.elim assump_107
    case inr assump_8 =>
      cases assump_8
      case intro assump_111 assump_112 =>
        cases assump_1
        case inl assump_117 =>
          have assump_174 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_123 := assump_3 assump_174
          apply False.elim assump_123
        case inr assump_118 =>
          cases assump_118
          case intro assump_127 assump_128 =>
            cases assump_127
            case inl assump_129 =>
              cases assump_129
              case inl assump_131 =>
                have assump_175 : (True ∨ p5) := by
                  apply Or.inl
                  apply True.intro
                let assump_140 := assump_3 assump_175
                apply False.elim assump_140
              case inr assump_132 =>
                have assump_176 : (p7 ∨ p4) := by
                  apply Or.inl
                  exact assump_132
                let assump_148 := assump_128 assump_176
                let assump_149 := And.left assump_148
                apply False.elim assump_149
            case inr assump_130 =>
              cases assump_130
              case intro assump_153 assump_154 =>
                have assump_177 : (p7 ∨ p4) := by
                  apply Or.inr
                  exact assump_153
                let assump_161 := assump_128 assump_177
                let assump_162 := And.left assump_161
                apply False.elim assump_162


variable (p5 p6 p2 p0 : Prop)
theorem file85_70359 : ((((((p0 → False) ∧ (p6 ∨ p5)) ∧ ((p2 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p0 → False) ∧ (p6 ∨ p5)) ∧ ((p2 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_34 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_18 := assump_7 assump_34
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_35 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_26 := assump_7 assump_35
          apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p3 p5 p6 p7 p1 p4 : Prop)
theorem file85_71258 : (((((p7 ∧ p6) ∧ (p7 ∨ p3)) ∧ ((False ∨ p5) ∧ (p7 → False))) → False) ∨ ((((p5 → False) ∨ (p4 ∧ True)) → ((p4 → False) → (p3 → False))) ∨ (((p7 ∨ p3) ∨ (p1 → p6)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              apply False.elim assump_18
            case inr assump_19 =>
              have assump_46 : p7 := by
                exact assump_12
              let assump_26 := assump_17 assump_46
              apply False.elim assump_26
        case inr assump_13 =>
          cases assump_3
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              apply False.elim assump_34
            case inr assump_35 =>
              have assump_47 : p7 := by
                exact assump_6
              let assump_42 := assump_33 assump_47
              apply False.elim assump_42


variable (p1 p3 p7 p6 p5 : Prop)
theorem file85_72513 : (((((p1 → False) → False) → ((False → p7) ∨ (p5 ∧ False))) → False) → ((((p1 ∧ p1) → (p1 → p3)) → ((p6 → True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_17 : (((p1 → False) → False) → ((False → p7) ∨ (p5 ∧ False))) := by
    intro assump_8
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_7 := assump_1 assump_17
  apply False.elim assump_7


variable (p3 p7 p0 : Prop)
theorem file85_72969 : (((((p0 ∧ p0) ∧ (True → False)) ∧ ((False ∨ p7) ∨ (False ∨ p7))) ∨ (((p0 → False) → (p3 → False)) ∧ ((False → p3) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              apply False.elim assump_18
            case inr assump_19 =>
              have assump_53 : True := by
                apply True.intro
              let assump_25 := assump_7 assump_53
              apply False.elim assump_25
          case inr assump_17 =>
            cases assump_17
            case inl assump_29 =>
              apply False.elim assump_29
            case inr assump_30 =>
              have assump_54 : True := by
                apply True.intro
              let assump_36 := assump_7 assump_54
              apply False.elim assump_36
  case inr assump_3 =>
    cases assump_3
    case intro assump_40 assump_41 =>
      have assump_55 : (False → p3) := by
        intro assump_47
        apply False.elim assump_47
      let assump_46 := assump_41 assump_55
      apply False.elim assump_46


variable (p6 p0 p5 p7 p1 : Prop)
theorem file85_74352 : ((((((True ∧ False) → (False → False)) → False) → (((p0 ∨ p6) → (p7 ∧ p5)) ∧ ((True ∨ p5) → (p1 → False)))) → False) → False) := by
  intro assump_5
  have assump_96 : ((((True ∧ False) → (False → False)) → False) → (((p0 ∨ p6) → (p7 ∧ p5)) ∧ ((True ∨ p5) → (p1 → False)))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    apply And.intro
    cases assump_10
    case inl assump_11 =>
      have assump_97 : ((True ∧ False) → (False → False)) := by
        intro assump_18
        intro assump_19
        apply False.elim assump_19
      let assump_17 := assump_9 assump_97
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_98 : ((True ∧ False) → (False → False)) := by
        intro assump_30
        intro assump_31
        apply False.elim assump_31
      let assump_29 := assump_9 assump_98
      apply False.elim assump_29
    cases assump_10
    case inl assump_37 =>
      have assump_99 : ((True ∧ False) → (False → False)) := by
        intro assump_44
        intro assump_45
        apply False.elim assump_45
      let assump_43 := assump_9 assump_99
      apply False.elim assump_43
    case inr assump_38 =>
      have assump_100 : ((True ∧ False) → (False → False)) := by
        intro assump_56
        intro assump_57
        apply False.elim assump_57
      let assump_55 := assump_9 assump_100
      apply False.elim assump_55
    intro assump_63
    intro assump_64
    cases assump_63
    case inl assump_67 =>
      have assump_101 : ((True ∧ False) → (False → False)) := by
        intro assump_74
        intro assump_75
        apply False.elim assump_75
      let assump_73 := assump_9 assump_101
      apply False.elim assump_73
    case inr assump_68 =>
      have assump_102 : ((True ∧ False) → (False → False)) := by
        intro assump_86
        intro assump_87
        apply False.elim assump_87
      let assump_85 := assump_9 assump_102
      apply False.elim assump_85
  let assump_8 := assump_5 assump_96
  apply False.elim assump_8


variable (p7 p6 p5 p2 p4 p3 p1 p0 : Prop)
theorem file85_76436 : (((((p3 → False) → False) → False) ∨ (((True → p6) → (p0 ∨ p7)) → False)) → ((((p5 ∧ p7) ∧ (True → False)) → ((p1 → p2) ∨ (p4 → p5))) ∨ (((p0 → False) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        have assump_46 : True := by
          apply True.intro
        let assump_21 := assump_8 assump_46
        apply False.elim assump_21
  case inr assump_3 =>
    apply Or.inl
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        apply Or.inl
        intro assump_38
        have assump_47 : True := by
          apply True.intro
        let assump_42 := assump_29 assump_47
        apply False.elim assump_42


variable (p0 p4 p7 p3 p2 : Prop)
theorem file85_77433 : ((((((False → False) → (p0 → p7)) ∧ ((p2 ∧ True) ∧ (p4 → False))) → (((False → p2) ∨ (p3 ∧ True)) ∧ ((p7 ∨ p2) ∨ (p7 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((False → False) → (p0 → p7)) ∧ ((p2 ∧ True) ∧ (p4 → False))) → (((False → p2) ∨ (p3 ∧ True)) ∧ ((p7 ∨ p2) ∨ (p7 ∧ p2)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          apply False.elim assump_20
    cases assump_5
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          apply Or.inl
          apply Or.inr
          exact assump_29
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p1 p2 p5 p4 p3 p7 p0 p6 : Prop)
theorem file85_78444 : (((((False → False) ∧ (p0 → True)) → ((p1 ∧ False) → False)) ∨ (((p5 ∨ False) → (p6 → p2)) → False)) ∨ ((((p0 → p0) → (False ∧ p4)) ∨ ((p0 → p4) ∨ (True ∧ p7))) → (((p6 → False) ∧ (p3 ∧ False)) ∨ ((p5 → p5) ∨ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p1 p3 p6 p5 p4 p7 p0 p2 : Prop)
theorem file85_78887 : (((((p5 ∧ p3) → False) ∧ ((p3 ∨ p1) → False)) → (((p2 ∧ False) → (p7 → p6)) → ((p3 → False) ∨ (p5 ∨ p4)))) ∧ ((((True → p5) → False) ∧ ((p5 ∧ p0) ∧ (p7 ∧ p2))) → (((p3 ∨ p7) → (p5 → p1)) ∧ ((p4 ∨ p4) → (p5 → False))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    have assump_156 : (p3 ∨ p1) := by
      apply Or.inl
      exact assump_11
    let assump_15 := assump_6 assump_156
    apply False.elim assump_15
  intro assump_19
  apply And.intro
  intro assump_20
  intro assump_21
  cases assump_20
  case inl assump_24 =>
    cases assump_19
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_33
          case intro assump_40 assump_41 =>
            have assump_157 : (True → p5) := by
              intro assump_51
              exact assump_34
            let assump_50 := assump_28 assump_157
            apply False.elim assump_50
  case inr assump_25 =>
    cases assump_19
    case intro assump_59 assump_60 =>
      cases assump_60
      case intro assump_63 assump_64 =>
        cases assump_63
        case intro assump_65 assump_66 =>
          cases assump_64
          case intro assump_71 assump_72 =>
            have assump_158 : (True → p5) := by
              intro assump_82
              exact assump_65
            let assump_81 := assump_59 assump_158
            apply False.elim assump_81
  intro assump_88
  intro assump_89
  cases assump_88
  case inl assump_92 =>
    cases assump_19
    case intro assump_96 assump_97 =>
      cases assump_97
      case intro assump_100 assump_101 =>
        cases assump_100
        case intro assump_102 assump_103 =>
          cases assump_101
          case intro assump_108 assump_109 =>
            have assump_159 : (True → p5) := by
              intro assump_119
              exact assump_102
            let assump_118 := assump_96 assump_159
            apply False.elim assump_118
  case inr assump_93 =>
    cases assump_19
    case intro assump_127 assump_128 =>
      cases assump_128
      case intro assump_131 assump_132 =>
        cases assump_131
        case intro assump_133 assump_134 =>
          cases assump_132
          case intro assump_139 assump_140 =>
            have assump_160 : (True → p5) := by
              intro assump_150
              exact assump_133
            let assump_149 := assump_127 assump_160
            apply False.elim assump_149


variable (p7 p5 p2 p4 p3 p0 p1 : Prop)
theorem file85_81546 : (((((p3 ∨ p1) → False) ∧ ((True → p0) ∧ (p1 ∧ p4))) → False) ∨ ((((p3 ∧ False) → (p7 → False)) → ((True ∧ p7) ∨ (p7 → False))) → (((p3 → p7) ∧ (p5 → p0)) → ((p2 ∨ p1) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : (p3 ∨ p1) := by
          apply Or.inr
          exact assump_10
        let assump_20 := assump_2 assump_24
        apply False.elim assump_20


variable (p3 p1 p7 p0 p4 p6 p2 : Prop)
theorem file85_82169 : (((((p7 → p1) ∨ (False ∨ p7)) ∨ ((p3 → False) → (p0 ∧ p1))) ∧ (((True → False) → (p1 → p7)) ∨ ((p3 ∨ p2) → (p1 ∨ p0)))) → ((((p1 → p3) → False) ∨ ((p4 ∧ p7) → (p6 → False))) → (((p2 ∧ p2) ∧ (p7 ∧ p7)) → ((False → False) → (p7 ∧ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_8
      case intro assump_15 assump_16 =>
        cases assump_2
        case inl assump_21 =>
          cases assump_1
          case intro assump_25 assump_26 =>
            cases assump_25
            case inl assump_27 =>
              cases assump_27
              case inl assump_29 =>
                cases assump_26
                case inl assump_33 =>
                  exact assump_16
                case inr assump_34 =>
                  exact assump_16
              case inr assump_30 =>
                cases assump_30
                case inl assump_39 =>
                  apply False.elim assump_39
                case inr assump_40 =>
                  cases assump_26
                  case inl assump_45 =>
                    exact assump_40
                  case inr assump_46 =>
                    exact assump_40
            case inr assump_28 =>
              cases assump_26
              case inl assump_53 =>
                exact assump_16
              case inr assump_54 =>
                exact assump_16
        case inr assump_22 =>
          cases assump_1
          case intro assump_61 assump_62 =>
            cases assump_61
            case inl assump_63 =>
              cases assump_63
              case inl assump_65 =>
                cases assump_62
                case inl assump_69 =>
                  exact assump_16
                case inr assump_70 =>
                  exact assump_16
              case inr assump_66 =>
                cases assump_66
                case inl assump_75 =>
                  apply False.elim assump_75
                case inr assump_76 =>
                  cases assump_62
                  case inl assump_81 =>
                    exact assump_76
                  case inr assump_82 =>
                    exact assump_76
            case inr assump_64 =>
              cases assump_62
              case inl assump_89 =>
                exact assump_16
              case inr assump_90 =>
                exact assump_16
  apply True.intro


variable (p3 p1 p2 p5 p7 p4 : Prop)
theorem file85_84725 : ((((((True ∨ p5) ∨ (p3 → p3)) ∨ ((p4 ∧ p2) ∨ (p1 → False))) ∨ (((p1 ∨ False) ∨ (p3 ∧ p7)) ∨ ((p7 ∨ p4) → (p7 → p4)))) → False) → False) := by
  intro assump_19
  have assump_26 : ((((True ∨ p5) ∨ (p3 → p3)) ∨ ((p4 ∧ p2) ∨ (p1 → False))) ∨ (((p1 ∨ False) ∨ (p3 ∧ p7)) ∨ ((p7 ∨ p4) → (p7 → p4)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_22 := assump_19 assump_26
  apply False.elim assump_22


variable (p5 p0 p2 p4 p1 p3 p7 : Prop)
theorem file85_85246 : (((((p0 ∨ p5) → False) ∧ ((True → False) ∧ (True ∨ p2))) ∧ (((p3 → False) ∨ (p0 ∧ False)) ∨ ((p7 ∧ p1) → False))) → ((((p4 ∨ False) → (p0 → False)) → False) → False)) := by
  intro assump_17
  intro assump_18
  cases assump_17
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_28
        case inl assump_31 =>
          cases assump_22
          case inl assump_35 =>
            cases assump_35
            case inl assump_37 =>
              have assump_87 : True := by
                apply True.intro
              let assump_42 := assump_27 assump_87
              apply False.elim assump_42
            case inr assump_38 =>
              cases assump_38
              case intro assump_46 assump_47 =>
                apply False.elim assump_47
          case inr assump_36 =>
            have assump_88 : True := by
              apply True.intro
            let assump_55 := assump_27 assump_88
            apply False.elim assump_55
        case inr assump_32 =>
          cases assump_22
          case inl assump_61 =>
            cases assump_61
            case inl assump_63 =>
              have assump_89 : True := by
                apply True.intro
              let assump_69 := assump_27 assump_89
              apply False.elim assump_69
            case inr assump_64 =>
              cases assump_64
              case intro assump_73 assump_74 =>
                apply False.elim assump_74
          case inr assump_62 =>
            have assump_90 : True := by
              apply True.intro
            let assump_83 := assump_27 assump_90
            apply False.elim assump_83


variable (p0 p3 p4 p6 p7 p5 : Prop)
theorem file85_87039 : (((((False → p4) → False) ∧ ((True → p3) ∧ (p5 → p6))) ∨ (((p0 → p0) → False) ∧ ((p7 → False) ∨ (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_50 : (False → p4) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_4 assump_50
        apply False.elim assump_17
  case inr assump_3 =>
    cases assump_3
    case intro assump_24 assump_25 =>
      cases assump_25
      case inl assump_28 =>
        have assump_51 : (p0 → p0) := by
          intro assump_34
          exact assump_34
        let assump_33 := assump_24 assump_51
        apply False.elim assump_33
      case inr assump_29 =>
        have assump_52 : (p0 → p0) := by
          intro assump_44
          exact assump_44
        let assump_43 := assump_24 assump_52
        apply False.elim assump_43


variable (p4 p6 p7 p1 p2 : Prop)
theorem file85_88084 : ((((((p1 → p4) → (True ∨ p4)) ∨ ((p1 ∧ p2) ∧ (False ∨ p7))) → (((p1 ∧ p4) ∨ (False ∨ False)) → ((p1 ∨ p6) → False))) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    have assump_39 : (((False → False) → False) → False) := by
      intro assump_26
      have assump_40 : (False → False) := by
        intro assump_30
        apply False.elim assump_30
      let assump_29 := assump_26 assump_40
      apply False.elim assump_29
    let assump_25 := assump_20 assump_39
    apply False.elim assump_25


variable (p6 p5 p2 p7 p4 : Prop)
theorem file85_88731 : ((((((p2 → False) ∨ (p6 ∨ False)) → ((False → p7) ∨ (p6 ∧ p4))) ∨ (((p5 ∨ p5) ∨ (p6 → False)) → ((p7 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p2 → False) ∨ (p6 ∨ False)) → ((False → p7) ∨ (p6 ∧ p4))) ∨ (((p5 ∨ p5) ∨ (p6 → False)) → ((p7 ∧ p5) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      case inr assump_14 =>
        apply False.elim assump_14
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p0 p5 p6 p2 : Prop)
theorem file85_89524 : ((((((True ∨ p0) ∧ (p0 ∧ p2)) ∨ ((p1 ∧ True) → False)) ∨ (((p6 → False) ∧ (p6 → False)) ∧ ((p6 → False) → False))) ∧ ((((p5 ∨ p6) → False) → ((p6 ∧ False) → False)) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_17
            case intro assump_22 assump_23 =>
              have assump_104 : (((p5 ∨ p6) → False) → ((p6 ∧ False) → False)) := by
                intro assump_31
                intro assump_32
                cases assump_32
                case intro assump_33 assump_34 =>
                  apply False.elim assump_34
              let assump_30 := assump_11 assump_104
              apply False.elim assump_30
          case inr assump_19 =>
            cases assump_17
            case intro assump_44 assump_45 =>
              have assump_105 : (((p5 ∨ p6) → False) → ((p6 ∧ False) → False)) := by
                intro assump_53
                intro assump_54
                cases assump_54
                case intro assump_55 assump_56 =>
                  apply False.elim assump_56
              let assump_52 := assump_11 assump_105
              apply False.elim assump_52
      case inr assump_15 =>
        have assump_106 : (((p5 ∨ p6) → False) → ((p6 ∧ False) → False)) := by
          intro assump_69
          intro assump_70
          cases assump_70
          case intro assump_71 assump_72 =>
            apply False.elim assump_72
        let assump_68 := assump_11 assump_106
        apply False.elim assump_68
    case inr assump_13 =>
      cases assump_13
      case intro assump_80 assump_81 =>
        cases assump_80
        case intro assump_82 assump_83 =>
          have assump_107 : (((p5 ∨ p6) → False) → ((p6 ∧ False) → False)) := by
            intro assump_93
            intro assump_94
            cases assump_94
            case intro assump_95 assump_96 =>
              apply False.elim assump_96
          let assump_92 := assump_11 assump_107
          apply False.elim assump_92


variable (p3 p7 p1 p5 : Prop)
theorem file85_91816 : ((((((True → p1) ∧ (True → False)) ∧ ((p5 ∧ p7) → (p3 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((True → p1) ∧ (True → False)) ∧ ((p5 ∧ p7) → (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_25 : True := by
          apply True.intro
        let assump_17 := assump_9 assump_25
        apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p6 p5 p3 p7 : Prop)
theorem file85_92422 : ((((((p7 ∧ p6) → False) ∨ ((p3 ∨ p5) → False)) → (((p3 → True) → False) → False)) → False) → False) := by
  intro assump_10
  have assump_39 : ((((p7 ∧ p6) → False) ∨ ((p3 ∨ p5) → False)) → (((p3 → True) → False) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_14
    case inl assump_18 =>
      have assump_40 : (p3 → True) := by
        intro assump_24
        apply True.intro
      let assump_23 := assump_15 assump_40
      apply False.elim assump_23
    case inr assump_19 =>
      have assump_41 : (p3 → True) := by
        intro assump_32
        apply True.intro
      let assump_31 := assump_15 assump_41
      apply False.elim assump_31
  let assump_13 := assump_10 assump_39
  apply False.elim assump_13


variable (p1 p7 p0 p6 p3 p4 p2 p5 : Prop)
theorem file85_93229 : (((((True ∧ p3) → (p4 ∧ p7)) ∧ ((p5 ∧ p0) ∧ (p0 → False))) ∨ (((p2 → p0) → (False ∨ p1)) → False)) → ((((p0 → p0) ∧ (p6 → False)) → ((p7 ∨ p3) → (p1 → True))) ∨ (((p0 → False) ∧ (p4 → False)) ∨ ((False → False) → (True → False))))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_22
          intro assump_23
          intro assump_24
          apply True.intro
  case inr assump_7 =>
    apply Or.inl
    intro assump_27
    intro assump_28
    intro assump_29
    apply True.intro


variable (p2 p1 p5 p0 p4 p6 p3 : Prop)
theorem file85_94018 : (((((p5 ∨ p0) → (p3 ∧ p2)) ∧ ((True ∧ p2) ∨ (p5 ∧ p3))) → (((True ∨ p1) ∨ (p0 ∨ p6)) ∨ ((p2 ∧ p1) ∧ (p0 → False)))) ∨ ((((p0 → False) → False) ∨ ((p3 ∨ p5) ∧ (p4 → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p3 p0 p6 p5 p1 p4 p7 : Prop)
theorem file85_94715 : (((((p5 → p3) ∨ (False ∨ p1)) → ((p1 ∨ p7) ∧ (p6 → False))) → (((p4 ∨ p0) → (p7 ∨ True)) ∧ ((True ∨ p1) ∧ (p6 → True)))) ∨ ((((p7 ∧ p4) → False) → False) ∧ (((p6 ∨ p0) ∧ (False ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    apply True.intro
  case inr assump_4 =>
    apply Or.inr
    apply True.intro
  apply And.intro
  apply Or.inl
  apply True.intro
  intro assump_15
  apply True.intro


variable (p3 p1 p4 p5 p0 p7 p6 p2 : Prop)
theorem file85_95280 : ((((((False → False) ∨ (p3 ∨ p2)) ∨ ((p7 → p0) → False)) ∧ (((p7 → False) → False) ∨ ((False ∨ p0) → (p5 → False)))) ∧ ((((p6 → False) ∨ (p4 ∧ True)) ∧ ((True → False) ∧ (p4 → False))) ∧ (((True ∨ p6) ∨ (True → p1)) → ((p0 ∨ p7) → (p2 ∧ p6))))) → False) := by
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
          case inl assump_12 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case inl assump_20 =>
                  cases assump_19
                  case intro assump_24 assump_25 =>
                    have assump_388 : True := by
                      apply True.intro
                    let assump_35 := assump_24 assump_388
                    apply False.elim assump_35
                case inr assump_21 =>
                  cases assump_21
                  case intro assump_39 assump_40 =>
                    cases assump_19
                    case intro assump_45 assump_46 =>
                      have assump_389 : p4 := by
                        exact assump_39
                      let assump_55 := assump_46 assump_389
                      apply False.elim assump_55
          case inr assump_13 =>
            cases assump_3
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_63
                case inl assump_65 =>
                  cases assump_64
                  case intro assump_69 assump_70 =>
                    have assump_390 : True := by
                      apply True.intro
                    let assump_80 := assump_69 assump_390
                    apply False.elim assump_80
                case inr assump_66 =>
                  cases assump_66
                  case intro assump_84 assump_85 =>
                    cases assump_64
                    case intro assump_90 assump_91 =>
                      have assump_391 : p4 := by
                        exact assump_84
                      let assump_100 := assump_91 assump_391
                      apply False.elim assump_100
        case inr assump_9 =>
          cases assump_9
          case inl assump_104 =>
            cases assump_5
            case inl assump_108 =>
              cases assump_3
              case intro assump_112 assump_113 =>
                cases assump_112
                case intro assump_114 assump_115 =>
                  cases assump_114
                  case inl assump_116 =>
                    cases assump_115
                    case intro assump_120 assump_121 =>
                      have assump_392 : True := by
                        apply True.intro
                      let assump_131 := assump_120 assump_392
                      apply False.elim assump_131
                  case inr assump_117 =>
                    cases assump_117
                    case intro assump_135 assump_136 =>
                      cases assump_115
                      case intro assump_141 assump_142 =>
                        have assump_393 : p4 := by
                          exact assump_135
                        let assump_151 := assump_142 assump_393
                        apply False.elim assump_151
            case inr assump_109 =>
              cases assump_3
              case intro assump_157 assump_158 =>
                cases assump_157
                case intro assump_159 assump_160 =>
                  cases assump_159
                  case inl assump_161 =>
                    cases assump_160
                    case intro assump_165 assump_166 =>
                      have assump_394 : True := by
                        apply True.intro
                      let assump_176 := assump_165 assump_394
                      apply False.elim assump_176
                  case inr assump_162 =>
                    cases assump_162
                    case intro assump_180 assump_181 =>
                      cases assump_160
                      case intro assump_186 assump_187 =>
                        have assump_395 : p4 := by
                          exact assump_180
                        let assump_196 := assump_187 assump_395
                        apply False.elim assump_196
          case inr assump_105 =>
            cases assump_5
            case inl assump_202 =>
              cases assump_3
              case intro assump_206 assump_207 =>
                cases assump_206
                case intro assump_208 assump_209 =>
                  cases assump_208
                  case inl assump_210 =>
                    cases assump_209
                    case intro assump_214 assump_215 =>
                      have assump_396 : True := by
                        apply True.intro
                      let assump_225 := assump_214 assump_396
                      apply False.elim assump_225
                  case inr assump_211 =>
                    cases assump_211
                    case intro assump_229 assump_230 =>
                      cases assump_209
                      case intro assump_235 assump_236 =>
                        have assump_397 : p4 := by
                          exact assump_229
                        let assump_245 := assump_236 assump_397
                        apply False.elim assump_245
            case inr assump_203 =>
              cases assump_3
              case intro assump_251 assump_252 =>
                cases assump_251
                case intro assump_253 assump_254 =>
                  cases assump_253
                  case inl assump_255 =>
                    cases assump_254
                    case intro assump_259 assump_260 =>
                      have assump_398 : True := by
                        apply True.intro
                      let assump_270 := assump_259 assump_398
                      apply False.elim assump_270
                  case inr assump_256 =>
                    cases assump_256
                    case intro assump_274 assump_275 =>
                      cases assump_254
                      case intro assump_280 assump_281 =>
                        have assump_399 : p4 := by
                          exact assump_274
                        let assump_290 := assump_281 assump_399
                        apply False.elim assump_290
      case inr assump_7 =>
        cases assump_5
        case inl assump_296 =>
          cases assump_3
          case intro assump_300 assump_301 =>
            cases assump_300
            case intro assump_302 assump_303 =>
              cases assump_302
              case inl assump_304 =>
                cases assump_303
                case intro assump_308 assump_309 =>
                  have assump_400 : True := by
                    apply True.intro
                  let assump_319 := assump_308 assump_400
                  apply False.elim assump_319
              case inr assump_305 =>
                cases assump_305
                case intro assump_323 assump_324 =>
                  cases assump_303
                  case intro assump_329 assump_330 =>
                    have assump_401 : p4 := by
                      exact assump_323
                    let assump_339 := assump_330 assump_401
                    apply False.elim assump_339
        case inr assump_297 =>
          cases assump_3
          case intro assump_345 assump_346 =>
            cases assump_345
            case intro assump_347 assump_348 =>
              cases assump_347
              case inl assump_349 =>
                cases assump_348
                case intro assump_353 assump_354 =>
                  have assump_402 : True := by
                    apply True.intro
                  let assump_364 := assump_353 assump_402
                  apply False.elim assump_364
              case inr assump_350 =>
                cases assump_350
                case intro assump_368 assump_369 =>
                  cases assump_348
                  case intro assump_374 assump_375 =>
                    have assump_403 : p4 := by
                      exact assump_368
                    let assump_384 := assump_375 assump_403
                    apply False.elim assump_384


variable (p3 p5 p4 : Prop)
theorem file85_103855 : ((((((True ∧ False) ∧ (p5 ∧ False)) ∧ ((p4 ∨ p3) → (False → False))) → False) → False) → False) := by
  intro assump_14
  have assump_32 : ((((True ∧ False) ∧ (p5 ∧ False)) ∧ ((p4 ∨ p3) → (False → False))) → False) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_24
  let assump_17 := assump_14 assump_32
  apply False.elim assump_17


variable (p4 p5 p7 p3 p0 p1 p2 : Prop)
theorem file85_104450 : ((((((p0 → p7) ∨ (p5 ∧ True)) ∧ ((True → p2) ∧ (p4 ∧ p0))) → (((p3 ∧ p2) ∧ (p5 → False)) ∨ ((p5 → p5) ∨ (p1 ∨ p1)))) → False) → False) := by
  intro assump_26
  have assump_72 : ((((p0 → p7) ∨ (p5 ∧ True)) ∧ ((True → p2) ∧ (p4 ∧ p0))) → (((p3 ∧ p2) ∧ (p5 → False)) ∨ ((p5 → p5) ∨ (p1 ∨ p1)))) := by
    intro assump_30
    cases assump_30
    case intro assump_31 assump_32 =>
      cases assump_31
      case inl assump_33 =>
        cases assump_32
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            apply Or.inr
            apply Or.inl
            intro assump_47
            exact assump_47
      case inr assump_34 =>
        cases assump_34
        case intro assump_50 assump_51 =>
          cases assump_32
          case intro assump_56 assump_57 =>
            cases assump_57
            case intro assump_60 assump_61 =>
              apply Or.inr
              apply Or.inl
              intro assump_66
              exact assump_66
  let assump_29 := assump_26 assump_72
  apply False.elim assump_29


variable (p3 p1 p7 p0 p6 p5 p2 : Prop)
theorem file85_105602 : (((((p5 → False) → (p2 → False)) → ((p5 ∨ True) → (False → p0))) → (((p2 ∨ p3) ∧ (p3 → p6)) ∨ ((p7 ∧ p7) → (p5 ∨ p6)))) → ((((p5 → False) ∨ (p1 ∨ True)) → ((p7 ∧ True) → (False → p2))) ∧ (((p2 → True) ∨ (p1 ∨ p0)) ∨ ((p6 → p6) ∨ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  apply Or.inl
  intro assump_9
  apply True.intro


variable (p5 p4 p2 p0 p3 p1 p6 : Prop)
theorem file85_106097 : (((((p1 ∧ p0) ∧ (p2 ∧ p5)) → ((p1 → False) ∨ (p6 → p2))) → False) → ((((p4 → False) ∨ (True ∧ p1)) → ((p1 ∧ False) → False)) ∨ (((True ∨ p3) ∨ (p3 ∨ p6)) ∨ ((p6 ∧ p4) ∧ (p2 → False))))) := by
  intro assump_53
  apply Or.inl
  intro assump_56
  intro assump_57
  cases assump_57
  case intro assump_58 assump_59 =>
    apply False.elim assump_59


variable (p6 p3 p4 p1 p7 p0 : Prop)
theorem file85_106503 : (((((p4 → p1) ∨ (p0 → False)) → False) ∧ (((p6 → False) ∧ (p6 ∧ p7)) ∧ ((p3 → True) → (p4 → p0)))) → ((((p1 → p0) → (p6 → p1)) ∨ ((p6 ∧ p0) → False)) ∨ (((p4 ∨ p1) → (True → p1)) ∨ ((False → False) ∧ (p7 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_20
          intro assump_21
          have assump_37 : p6 := by
            exact assump_21
          let assump_33 := assump_8 assump_37
          apply False.elim assump_33


variable (p0 p4 p6 p5 p3 p2 : Prop)
theorem file85_107275 : ((((((p0 → False) → (p5 → False)) → ((False → False) ∨ (False ∨ p0))) → (((p3 ∨ True) ∨ (p2 → False)) ∨ ((False ∨ p3) → (False → p6)))) ∧ ((((p0 ∨ True) ∨ (p4 ∨ p2)) → ((True ∨ p2) → (p4 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p0 ∨ True) ∨ (p4 ∨ p2)) → ((True ∨ p2) → (p4 → True))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p2 p3 p4 p6 p1 p5 p7 : Prop)
theorem file85_107870 : (((((True ∧ p1) → (p3 ∨ False)) ∨ ((p3 → p3) ∨ (p2 ∨ p4))) → False) → ((((True ∨ p2) ∨ (p5 → False)) ∨ ((p7 ∧ p3) ∧ (False ∧ p3))) ∨ (((p5 ∨ p6) ∧ (True ∧ p5)) → ((p1 ∧ p4) → (p3 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p2 p0 p4 p3 p5 p1 : Prop)
theorem file85_108224 : (((((False ∧ p5) ∧ (p4 ∧ p3)) → False) ∨ (((p1 ∧ p4) ∧ (p0 → False)) ∧ ((p1 → True) ∧ (p2 → True)))) ∧ ((((True → False) → (p3 → False)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4
  intro assump_8
  have assump_25 : ((True → False) → (p3 → False)) := by
    intro assump_12
    intro assump_13
    have assump_26 : True := by
      apply True.intro
    let assump_18 := assump_12 assump_26
    apply False.elim assump_18
  let assump_11 := assump_8 assump_25
  apply False.elim assump_11


variable (p7 p2 p6 : Prop)
theorem file85_108933 : ((((((p2 ∧ p2) ∧ (p6 ∧ False)) → ((True → False) → False)) → (((False → p7) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p2 ∧ p2) ∧ (p6 ∧ False)) → ((True → False) → False)) → (((False → p7) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_23 : (False → p7) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_6 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p0 p6 p1 p5 p3 p7 p2 : Prop)
theorem file85_109522 : ((((((True ∨ False) → (p1 → False)) ∧ ((p7 ∧ p4) ∧ (False ∧ p3))) ∧ (((p5 ∧ p2) ∨ (p1 → False)) ∧ ((False → p6) → False))) ∧ ((((p6 ∨ p7) → (p0 ∧ p5)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p5 p4 p7 p0 : Prop)
theorem file85_110193 : ((((((False → False) → False) → False) ∨ (((p5 ∨ p0) ∨ (p4 → p0)) → ((p7 → False) → (p7 → p5)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p5 ∨ p0) ∨ (p4 → p0)) → ((p7 → False) → (p7 → p5)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p1 p0 p2 : Prop)
theorem file85_110771 : ((((((p6 → False) → (True ∨ False)) ∨ ((p2 → False) ∨ (p0 ∧ p2))) ∨ (((p0 → False) ∨ (p1 ∧ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 → False) → (True ∨ False)) ∨ ((p2 → False) ∨ (p0 ∧ p2))) ∨ (((p0 → False) ∨ (p1 ∧ p0)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p1 p7 p4 p0 : Prop)
theorem file85_111260 : (((((p4 → p4) ∧ (False → p7)) → ((True → False) ∧ (p6 → p0))) → False) ∨ ((((False ∧ False) ∧ (p1 → False)) → ((p4 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_23
  have assump_38 : ((p4 → p4) ∧ (False → p7)) := by
    apply And.intro
    intro assump_27
    exact assump_27
    intro assump_30
    apply False.elim assump_30
  let assump_26 := assump_23 assump_38
  let assump_33 := And.left assump_26
  have assump_39 : True := by
    apply True.intro
  let assump_34 := assump_33 assump_39
  apply False.elim assump_34


variable (p3 p4 p7 p5 : Prop)
theorem file85_111856 : ((((((p3 → False) ∧ (p5 → p4)) ∨ ((p7 ∧ False) → False)) → (((True → True) ∧ (True → False)) → False)) → False) → False) := by
  intro assump_19
  have assump_55 : ((((p3 → False) ∧ (p5 → p4)) ∨ ((p7 ∧ False) → False)) → (((True → True) ∧ (True → False)) → False)) := by
    intro assump_23
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      cases assump_23
      case inl assump_31 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          have assump_56 : True := by
            apply True.intro
          let assump_41 := assump_26 assump_56
          apply False.elim assump_41
      case inr assump_32 =>
        have assump_57 : True := by
          apply True.intro
        let assump_48 := assump_26 assump_57
        apply False.elim assump_48
  let assump_22 := assump_19 assump_55
  apply False.elim assump_22


variable (p5 p1 p7 p2 p4 : Prop)
theorem file85_112788 : (((((p2 → False) ∧ (p5 ∧ True)) ∧ ((False → p4) → False)) → False) ∨ ((((p1 ∨ p4) ∧ (p4 → p7)) → ((p2 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_23 : (False → p4) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p0 p1 p2 p7 p6 p4 p3 p5 : Prop)
theorem file85_113374 : (((((False ∨ p6) ∧ (p4 → False)) ∧ ((p3 → False) → False)) ∧ (((False → p0) ∨ (p2 → p6)) → False)) → ((((p1 ∨ p4) ∨ (p5 → p2)) ∨ ((p4 ∧ p0) ∨ (p0 → False))) ∨ (((p3 ∧ p7) ∧ (False → False)) ∧ ((p2 ∨ True) → (p1 → p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          intro assump_20
          have assump_31 : ((False → p0) ∨ (p2 → p6)) := by
            apply Or.inl
            intro assump_25
            apply False.elim assump_25
          let assump_24 := assump_3 assump_31
          apply False.elim assump_24


variable (p2 p6 p0 : Prop)
theorem file85_114281 : ((((((True → False) → False) → False) → (((p0 → p6) ∧ (p2 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) → False) → False) → (((p0 → p6) ∧ (p2 ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_34 : ((True → False) → False) := by
          intro assump_20
          have assump_35 : True := by
            apply True.intro
          let assump_23 := assump_20 assump_35
          apply False.elim assump_23
        let assump_19 := assump_5 assump_34
        apply False.elim assump_19
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p2 p1 p5 p6 p4 p7 : Prop)
theorem file85_115086 : ((((((p1 ∧ False) → (True ∨ p7)) ∨ ((p4 → p5) ∨ (p4 ∧ p2))) ∨ (((p2 → p6) ∧ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∧ False) → (True ∨ p7)) ∨ ((p4 → p5) ∨ (p4 ∧ p2))) ∨ (((p2 → p6) ∧ (p4 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p7 p1 p3 p2 p5 p6 p0 : Prop)
theorem file85_115621 : (((((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) → (((p4 ∨ True) → False) ∧ ((p0 → False) ∧ (p7 ∨ p5)))) → ((((p6 ∨ p6) → False) ∧ ((p7 → False) → (p7 ∧ False))) ∨ (((p1 → p3) → (p5 ∧ p4)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_88 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_11
      have assump_89 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        exact assump_11
        exact assump_11
      let assump_16 := assump_1 assump_89
      let assump_17 := And.left assump_16
      have assump_90 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_18 := assump_17 assump_90
      apply False.elim assump_18
    let assump_10 := assump_1 assump_88
    let assump_22 := And.left assump_10
    have assump_91 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_23 := assump_22 assump_91
    apply False.elim assump_23
  case inr assump_6 =>
    have assump_92 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_31
      have assump_93 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
        apply Or.inl
        apply Or.inl
        apply And.intro
        exact assump_31
        exact assump_31
      let assump_36 := assump_1 assump_93
      let assump_37 := And.left assump_36
      have assump_94 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_38 := assump_37 assump_94
      apply False.elim assump_38
    let assump_30 := assump_1 assump_92
    let assump_42 := And.left assump_30
    have assump_95 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_43 := assump_42 assump_95
    apply False.elim assump_43
  intro assump_47
  apply And.intro
  have assump_96 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_52
    have assump_97 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_52
      exact assump_52
    let assump_57 := assump_1 assump_97
    let assump_58 := And.left assump_57
    have assump_98 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_59 := assump_58 assump_98
    apply False.elim assump_59
  let assump_51 := assump_1 assump_96
  let assump_63 := And.left assump_51
  have assump_99 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_64 := assump_63 assump_99
  apply False.elim assump_64
  have assump_100 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_72
    have assump_101 : (((p2 ∧ p2) ∨ (p2 → False)) ∨ ((False ∧ p5) ∧ (p2 → False))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_72
      exact assump_72
    let assump_77 := assump_1 assump_101
    let assump_78 := And.left assump_77
    have assump_102 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_79 := assump_78 assump_102
    apply False.elim assump_79
  let assump_71 := assump_1 assump_100
  let assump_83 := And.left assump_71
  have assump_103 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_84 := assump_83 assump_103
  apply False.elim assump_84


variable (p4 p6 p1 p0 p7 : Prop)
theorem file85_119304 : (((((p7 ∨ p7) ∨ (False → False)) ∨ ((p0 → False) ∨ (p1 ∨ p0))) ∨ (((True ∧ p6) ∧ (p6 → False)) ∧ ((True → p6) ∧ (p0 ∧ p4)))) → ((((p4 → False) ∧ (True → False)) → ((p7 → p4) → (p4 → False))) ∨ (((True ∧ p7) → (p1 → p0)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply Or.inl
          intro assump_12
          intro assump_13
          intro assump_14
          cases assump_12
          case intro assump_19 assump_20 =>
            have assump_167 : True := by
              apply True.intro
            let assump_25 := assump_20 assump_167
            apply False.elim assump_25
        case inr assump_9 =>
          apply Or.inl
          intro assump_31
          intro assump_32
          intro assump_33
          cases assump_31
          case intro assump_38 assump_39 =>
            have assump_168 : True := by
              apply True.intro
            let assump_44 := assump_39 assump_168
            apply False.elim assump_44
      case inr assump_7 =>
        apply Or.inl
        intro assump_50
        intro assump_51
        intro assump_52
        cases assump_50
        case intro assump_57 assump_58 =>
          have assump_169 : True := by
            apply True.intro
          let assump_63 := assump_58 assump_169
          apply False.elim assump_63
    case inr assump_5 =>
      cases assump_5
      case inl assump_67 =>
        apply Or.inl
        intro assump_71
        intro assump_72
        intro assump_73
        cases assump_71
        case intro assump_78 assump_79 =>
          have assump_170 : True := by
            apply True.intro
          let assump_84 := assump_79 assump_170
          apply False.elim assump_84
      case inr assump_68 =>
        cases assump_68
        case inl assump_88 =>
          apply Or.inl
          intro assump_92
          intro assump_93
          intro assump_94
          cases assump_92
          case intro assump_99 assump_100 =>
            have assump_171 : True := by
              apply True.intro
            let assump_105 := assump_100 assump_171
            apply False.elim assump_105
        case inr assump_89 =>
          apply Or.inl
          intro assump_111
          intro assump_112
          intro assump_113
          cases assump_111
          case intro assump_118 assump_119 =>
            have assump_172 : True := by
              apply True.intro
            let assump_124 := assump_119 assump_172
            apply False.elim assump_124
  case inr assump_3 =>
    cases assump_3
    case intro assump_128 assump_129 =>
      cases assump_128
      case intro assump_130 assump_131 =>
        cases assump_130
        case intro assump_132 assump_133 =>
          cases assump_129
          case intro assump_140 assump_141 =>
            cases assump_141
            case intro assump_144 assump_145 =>
              apply Or.inl
              intro assump_150
              intro assump_151
              intro assump_152
              cases assump_150
              case intro assump_157 assump_158 =>
                have assump_173 : True := by
                  apply True.intro
                let assump_163 := assump_158 assump_173
                apply False.elim assump_163


variable (p1 p7 p4 p3 : Prop)
theorem file85_122750 : (((((p3 → False) → (False → False)) → False) → False) ∨ ((((p3 ∧ p4) → (p7 ∧ True)) ∨ ((p4 → False) → (p3 → False))) ∧ (((p3 → False) → False) ∧ ((True → True) → (p3 ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((p3 → False) → (False → False)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p2 p0 p7 p4 p5 p6 : Prop)
theorem file85_123218 : (((((p2 → p5) → (False → p1)) ∨ ((p4 ∨ p7) ∧ (p4 → p0))) ∨ (((p7 ∧ False) ∧ (p7 → p6)) → False)) ∨ ((((p6 ∧ False) → False) → False) ∧ (((p6 ∨ p1) ∨ (True ∨ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p0 p3 p1 p6 p4 p7 p2 p5 : Prop)
theorem file85_123570 : ((((((p1 → False) ∨ (p0 → p5)) ∧ ((p6 → False) ∧ (False ∧ p3))) ∧ (((p5 ∧ p2) ∧ (p2 ∧ True)) → ((p6 ∨ p2) ∧ (p3 ∧ p0)))) ∨ ((((p4 → p6) → (True ∨ p7)) → ((p0 ∨ p1) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
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
  case inr assump_3 =>
    have assump_42 : (((p4 → p6) → (True ∨ p7)) → ((p0 ∨ p1) ∨ (False → False))) := by
      intro assump_33
      apply Or.inr
      intro assump_36
      apply False.elim assump_36
    let assump_32 := assump_3 assump_42
    apply False.elim assump_32


variable (p4 p2 p5 p6 p0 p7 p3 : Prop)
theorem file85_124739 : ((((((p7 → p2) ∧ (p6 → False)) ∧ ((p4 → p5) ∨ (p5 ∨ p7))) → (((p3 ∧ p6) → False) ∨ ((p3 → p0) → (p5 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_69 : ((((p7 → p2) ∧ (p6 → False)) ∧ ((p4 → p5) ∨ (p5 ∨ p7))) → (((p3 ∧ p6) → False) ∨ ((p3 → p0) → (p5 ∧ False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            have assump_70 : p6 := by
              exact assump_20
            let assump_28 := assump_9 assump_70
            apply False.elim assump_28
        case inr assump_15 =>
          cases assump_15
          case inl assump_32 =>
            apply Or.inl
            intro assump_36
            cases assump_36
            case intro assump_37 assump_38 =>
              have assump_71 : p6 := by
                exact assump_38
              let assump_46 := assump_9 assump_71
              apply False.elim assump_46
          case inr assump_33 =>
            apply Or.inl
            intro assump_52
            cases assump_52
            case intro assump_53 assump_54 =>
              have assump_72 : p6 := by
                exact assump_54
              let assump_62 := assump_9 assump_72
              apply False.elim assump_62
  let assump_4 := assump_1 assump_69
  apply False.elim assump_4


variable (p3 p4 p1 p2 p6 p5 p7 p0 : Prop)
theorem file85_126318 : (((((p0 ∧ p5) → (p0 → p4)) → False) ∨ (((p0 ∨ False) ∨ (p2 → False)) ∨ ((p1 ∧ p0) → False))) → ((((p5 ∧ p3) ∨ (p4 → p5)) ∧ ((p4 → p7) ∨ (p5 → p6))) → (((p6 ∧ p2) → (p3 → p6)) ∨ ((False ∧ True) ∨ (True ∨ p1))))) := by
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
          case inl assump_17 =>
            apply Or.inl
            intro assump_21
            intro assump_22
            cases assump_21
            case intro assump_25 assump_26 =>
              exact assump_25
          case inr assump_18 =>
            cases assump_18
            case inl assump_31 =>
              cases assump_31
              case inl assump_33 =>
                cases assump_33
                case inl assump_35 =>
                  apply Or.inl
                  intro assump_39
                  intro assump_40
                  cases assump_39
                  case intro assump_43 assump_44 =>
                    exact assump_43
                case inr assump_36 =>
                  apply False.elim assump_36
              case inr assump_34 =>
                apply Or.inl
                intro assump_53
                intro assump_54
                cases assump_53
                case intro assump_57 assump_58 =>
                  exact assump_57
            case inr assump_32 =>
              apply Or.inl
              intro assump_65
              intro assump_66
              cases assump_65
              case intro assump_69 assump_70 =>
                exact assump_69
        case inr assump_14 =>
          cases assump_1
          case inl assump_77 =>
            apply Or.inl
            intro assump_81
            intro assump_82
            cases assump_81
            case intro assump_85 assump_86 =>
              exact assump_85
          case inr assump_78 =>
            cases assump_78
            case inl assump_91 =>
              cases assump_91
              case inl assump_93 =>
                cases assump_93
                case inl assump_95 =>
                  apply Or.inl
                  intro assump_99
                  intro assump_100
                  cases assump_99
                  case intro assump_103 assump_104 =>
                    exact assump_103
                case inr assump_96 =>
                  apply False.elim assump_96
              case inr assump_94 =>
                apply Or.inl
                intro assump_113
                intro assump_114
                cases assump_113
                case intro assump_117 assump_118 =>
                  exact assump_117
            case inr assump_92 =>
              apply Or.inl
              intro assump_125
              intro assump_126
              cases assump_125
              case intro assump_129 assump_130 =>
                exact assump_129
    case inr assump_6 =>
      cases assump_4
      case inl assump_137 =>
        cases assump_1
        case inl assump_141 =>
          apply Or.inl
          intro assump_145
          intro assump_146
          cases assump_145
          case intro assump_149 assump_150 =>
            exact assump_149
        case inr assump_142 =>
          cases assump_142
          case inl assump_155 =>
            cases assump_155
            case inl assump_157 =>
              cases assump_157
              case inl assump_159 =>
                apply Or.inl
                intro assump_163
                intro assump_164
                cases assump_163
                case intro assump_167 assump_168 =>
                  exact assump_167
              case inr assump_160 =>
                apply False.elim assump_160
            case inr assump_158 =>
              apply Or.inl
              intro assump_177
              intro assump_178
              cases assump_177
              case intro assump_181 assump_182 =>
                exact assump_181
          case inr assump_156 =>
            apply Or.inl
            intro assump_189
            intro assump_190
            cases assump_189
            case intro assump_193 assump_194 =>
              exact assump_193
      case inr assump_138 =>
        cases assump_1
        case inl assump_201 =>
          apply Or.inl
          intro assump_205
          intro assump_206
          cases assump_205
          case intro assump_209 assump_210 =>
            exact assump_209
        case inr assump_202 =>
          cases assump_202
          case inl assump_215 =>
            cases assump_215
            case inl assump_217 =>
              cases assump_217
              case inl assump_219 =>
                apply Or.inl
                intro assump_223
                intro assump_224
                cases assump_223
                case intro assump_227 assump_228 =>
                  exact assump_227
              case inr assump_220 =>
                apply False.elim assump_220
            case inr assump_218 =>
              apply Or.inl
              intro assump_237
              intro assump_238
              cases assump_237
              case intro assump_241 assump_242 =>
                exact assump_241
          case inr assump_216 =>
            apply Or.inl
            intro assump_249
            intro assump_250
            cases assump_249
            case intro assump_253 assump_254 =>
              exact assump_253


variable (p2 p5 p4 : Prop)
theorem file85_131909 : ((((((True → False) ∧ (p2 ∨ False)) → False) ∨ (((p5 ∨ p4) ∧ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_24 : ((((True → False) ∧ (p2 ∨ False)) → False) ∨ (((p5 ∨ p4) ∧ (p4 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_25 : True := by
          apply True.intro
        let assump_15 := assump_6 assump_25
        apply False.elim assump_15
      case inr assump_11 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p5 p7 p2 p0 p6 p1 p3 p4 : Prop)
theorem file85_132619 : ((((((p0 ∧ p2) → False) → False) ∨ (((p6 → p5) ∧ (p3 ∧ p1)) ∧ ((p5 → False) ∧ (p5 → True)))) ∧ ((((p3 ∨ p3) ∧ (False → p4)) ∨ ((p0 → p7) → (p2 ∧ False))) ∧ (((False ∨ True) → False) ∧ ((True ∧ p7) ∨ (p0 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_9
              case intro assump_20 assump_21 =>
                cases assump_21
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    have assump_260 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_33 := assump_20 assump_260
                    apply False.elim assump_33
                case inr assump_25 =>
                  cases assump_25
                  case inl assump_37 =>
                    have assump_261 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_42 := assump_20 assump_261
                    apply False.elim assump_42
                  case inr assump_38 =>
                    have assump_262 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_49 := assump_20 assump_262
                    apply False.elim assump_49
            case inr assump_15 =>
              cases assump_9
              case intro assump_57 assump_58 =>
                cases assump_58
                case inl assump_61 =>
                  cases assump_61
                  case intro assump_63 assump_64 =>
                    have assump_263 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_70 := assump_57 assump_263
                    apply False.elim assump_70
                case inr assump_62 =>
                  cases assump_62
                  case inl assump_74 =>
                    have assump_264 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_79 := assump_57 assump_264
                    apply False.elim assump_79
                  case inr assump_75 =>
                    have assump_265 : (False ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_86 := assump_57 assump_265
                    apply False.elim assump_86
        case inr assump_11 =>
          cases assump_9
          case intro assump_92 assump_93 =>
            cases assump_93
            case inl assump_96 =>
              cases assump_96
              case intro assump_98 assump_99 =>
                have assump_266 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_105 := assump_92 assump_266
                apply False.elim assump_105
            case inr assump_97 =>
              cases assump_97
              case inl assump_109 =>
                have assump_267 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_114 := assump_92 assump_267
                apply False.elim assump_114
              case inr assump_110 =>
                have assump_268 : (False ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_121 := assump_92 assump_268
                apply False.elim assump_121
    case inr assump_5 =>
      cases assump_5
      case intro assump_125 assump_126 =>
        cases assump_125
        case intro assump_127 assump_128 =>
          cases assump_128
          case intro assump_131 assump_132 =>
            cases assump_126
            case intro assump_137 assump_138 =>
              cases assump_3
              case intro assump_143 assump_144 =>
                cases assump_143
                case inl assump_145 =>
                  cases assump_145
                  case intro assump_147 assump_148 =>
                    cases assump_147
                    case inl assump_149 =>
                      cases assump_144
                      case intro assump_155 assump_156 =>
                        cases assump_156
                        case inl assump_159 =>
                          cases assump_159
                          case intro assump_161 assump_162 =>
                            have assump_269 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_168 := assump_155 assump_269
                            apply False.elim assump_168
                        case inr assump_160 =>
                          cases assump_160
                          case inl assump_172 =>
                            have assump_270 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_177 := assump_155 assump_270
                            apply False.elim assump_177
                          case inr assump_173 =>
                            have assump_271 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_184 := assump_155 assump_271
                            apply False.elim assump_184
                    case inr assump_150 =>
                      cases assump_144
                      case intro assump_192 assump_193 =>
                        cases assump_193
                        case inl assump_196 =>
                          cases assump_196
                          case intro assump_198 assump_199 =>
                            have assump_272 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_205 := assump_192 assump_272
                            apply False.elim assump_205
                        case inr assump_197 =>
                          cases assump_197
                          case inl assump_209 =>
                            have assump_273 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_214 := assump_192 assump_273
                            apply False.elim assump_214
                          case inr assump_210 =>
                            have assump_274 : (False ∨ True) := by
                              apply Or.inr
                              apply True.intro
                            let assump_221 := assump_192 assump_274
                            apply False.elim assump_221
                case inr assump_146 =>
                  cases assump_144
                  case intro assump_227 assump_228 =>
                    cases assump_228
                    case inl assump_231 =>
                      cases assump_231
                      case intro assump_233 assump_234 =>
                        have assump_275 : (False ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_240 := assump_227 assump_275
                        apply False.elim assump_240
                    case inr assump_232 =>
                      cases assump_232
                      case inl assump_244 =>
                        have assump_276 : (False ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_249 := assump_227 assump_276
                        apply False.elim assump_249
                      case inr assump_245 =>
                        have assump_277 : (False ∨ True) := by
                          apply Or.inr
                          apply True.intro
                        let assump_256 := assump_227 assump_277
                        apply False.elim assump_256


variable (p2 p3 p4 p0 p1 p5 p7 : Prop)
theorem file85_141107 : (((((False ∨ p0) ∧ (p1 ∧ False)) ∨ ((True ∨ False) ∧ (p0 ∨ p1))) → (((p7 ∧ p5) → False) → ((p3 ∨ False) → (p4 → False)))) → ((((False → False) ∨ (p2 → False)) ∧ ((True → False) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        have assump_37 : True := by
          apply True.intro
        let assump_18 := assump_10 assump_37
        apply False.elim assump_18
    case inr assump_6 =>
      cases assump_4
      case intro assump_24 assump_25 =>
        have assump_38 : True := by
          apply True.intro
        let assump_33 := assump_25 assump_38
        apply False.elim assump_33


variable (p2 p5 p3 p7 p0 p1 p4 : Prop)
theorem file85_141943 : (((((p4 → p1) → False) → ((False → p0) → (p1 → False))) → False) → ((((p3 ∨ p1) ∨ (p7 → False)) → ((p2 → False) ∧ (True ∧ p5))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_27 : (((p4 → p1) → False) → ((False → p0) → (p1 → False))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    have assump_28 : (p4 → p1) := by
      intro assump_18
      exact assump_10
    let assump_17 := assump_8 assump_28
    apply False.elim assump_17
  let assump_7 := assump_1 assump_27
  apply False.elim assump_7


variable (p0 p7 p5 p4 p6 p3 : Prop)
theorem file85_142535 : ((((((p5 ∨ p5) → False) → ((False → p7) ∨ (p4 ∨ p3))) ∧ (((p7 ∨ True) ∨ (p7 ∧ p0)) ∧ ((False → p6) → (p6 ∨ True)))) → False) → False) := by
  intro assump_17
  have assump_33 : ((((p5 ∨ p5) → False) → ((False → p7) ∨ (p4 ∨ p3))) ∧ (((p7 ∨ True) ∨ (p7 ∧ p0)) ∧ ((False → p6) → (p6 ∨ True)))) := by
    apply And.intro
    intro assump_21
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
    apply And.intro
    apply Or.inl
    apply Or.inr
    apply True.intro
    intro assump_27
    apply Or.inr
    apply True.intro
  let assump_20 := assump_17 assump_33
  apply False.elim assump_20


variable (p0 p7 p1 p4 : Prop)
theorem file85_143195 : ((((((p4 ∧ False) → False) ∨ ((p0 → p1) → (p7 → False))) ∨ (((p4 → False) ∨ (p0 ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 ∧ False) → False) ∨ ((p0 → p1) → (p7 → False))) ∨ (((p4 → False) ∨ (p0 ∧ p7)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p7 p2 : Prop)
theorem file85_143709 : (((((True → False) → (True ∨ p7)) ∨ ((p7 ∧ p6) → (p6 → p2))) → False) → False) := by
  intro assump_1
  have assump_11 : (((True → False) → (True ∨ p7)) ∨ ((p7 ∧ p6) → (p6 → p2))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


