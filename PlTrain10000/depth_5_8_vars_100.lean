variable (p6 : Prop)
theorem file100_29 : ((((((False ∨ False) → (p6 → False)) → False) → False) → False) → False) := by
  intro assump_33
  have assump_57 : ((((False ∨ False) → (p6 → False)) → False) → False) := by
    intro assump_37
    have assump_58 : ((False ∨ False) → (p6 → False)) := by
      intro assump_41
      intro assump_42
      cases assump_41
      case inl assump_45 =>
        apply False.elim assump_45
      case inr assump_46 =>
        apply False.elim assump_46
    let assump_40 := assump_37 assump_58
    apply False.elim assump_40
  let assump_36 := assump_33 assump_57
  apply False.elim assump_36


variable (p6 p1 p5 p2 p7 p4 : Prop)
theorem file100_676 : (((((p2 ∨ p2) ∨ (False → p6)) → False) → False) ∨ ((((p7 → False) → False) → False) ∧ (((p1 → p2) → (p5 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p2 ∨ p2) ∨ (False → p6)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p4 p0 p6 p2 p1 p5 : Prop)
theorem file100_1082 : (((((False → False) ∧ (p2 ∨ p3)) ∧ ((True ∧ p1) → (p1 ∨ p0))) ∧ (((p6 ∧ False) ∧ (p0 ∨ p5)) ∧ ((p5 → p1) ∨ (True → False)))) → ((((p1 ∨ p4) ∧ (p5 → False)) → ((p0 → p4) ∧ (p2 ∧ False))) → (((p3 ∧ p1) ∨ (p1 ∨ p0)) → ((p0 ∨ p4) → (p4 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_1
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              cases assump_27
              case inl assump_30 =>
                cases assump_23
                case intro assump_36 assump_37 =>
                  cases assump_36
                  case intro assump_38 assump_39 =>
                    cases assump_38
                    case intro assump_40 assump_41 =>
                      apply False.elim assump_41
              case inr assump_31 =>
                cases assump_23
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    cases assump_52
                    case intro assump_54 assump_55 =>
                      apply False.elim assump_55
    case inr assump_13 =>
      cases assump_13
      case inl assump_60 =>
        cases assump_1
        case intro assump_66 assump_67 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_71
              case inl assump_74 =>
                cases assump_67
                case intro assump_80 assump_81 =>
                  cases assump_80
                  case intro assump_82 assump_83 =>
                    cases assump_82
                    case intro assump_84 assump_85 =>
                      apply False.elim assump_85
              case inr assump_75 =>
                cases assump_67
                case intro assump_94 assump_95 =>
                  cases assump_94
                  case intro assump_96 assump_97 =>
                    cases assump_96
                    case intro assump_98 assump_99 =>
                      apply False.elim assump_99
      case inr assump_61 =>
        cases assump_1
        case intro assump_108 assump_109 =>
          cases assump_108
          case intro assump_110 assump_111 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              cases assump_113
              case inl assump_116 =>
                cases assump_109
                case intro assump_122 assump_123 =>
                  cases assump_122
                  case intro assump_124 assump_125 =>
                    cases assump_124
                    case intro assump_126 assump_127 =>
                      apply False.elim assump_127
              case inr assump_117 =>
                cases assump_109
                case intro assump_136 assump_137 =>
                  cases assump_136
                  case intro assump_138 assump_139 =>
                    cases assump_138
                    case intro assump_140 assump_141 =>
                      apply False.elim assump_141
  case inr assump_9 =>
    cases assump_3
    case inl assump_148 =>
      cases assump_148
      case intro assump_150 assump_151 =>
        cases assump_1
        case intro assump_158 assump_159 =>
          cases assump_158
          case intro assump_160 assump_161 =>
            cases assump_160
            case intro assump_162 assump_163 =>
              cases assump_163
              case inl assump_166 =>
                cases assump_159
                case intro assump_172 assump_173 =>
                  cases assump_172
                  case intro assump_174 assump_175 =>
                    cases assump_174
                    case intro assump_176 assump_177 =>
                      apply False.elim assump_177
              case inr assump_167 =>
                cases assump_159
                case intro assump_186 assump_187 =>
                  cases assump_186
                  case intro assump_188 assump_189 =>
                    cases assump_188
                    case intro assump_190 assump_191 =>
                      apply False.elim assump_191
    case inr assump_149 =>
      cases assump_149
      case inl assump_196 =>
        cases assump_1
        case intro assump_202 assump_203 =>
          cases assump_202
          case intro assump_204 assump_205 =>
            cases assump_204
            case intro assump_206 assump_207 =>
              cases assump_207
              case inl assump_210 =>
                cases assump_203
                case intro assump_216 assump_217 =>
                  cases assump_216
                  case intro assump_218 assump_219 =>
                    cases assump_218
                    case intro assump_220 assump_221 =>
                      apply False.elim assump_221
              case inr assump_211 =>
                cases assump_203
                case intro assump_230 assump_231 =>
                  cases assump_230
                  case intro assump_232 assump_233 =>
                    cases assump_232
                    case intro assump_234 assump_235 =>
                      apply False.elim assump_235
      case inr assump_197 =>
        cases assump_1
        case intro assump_244 assump_245 =>
          cases assump_244
          case intro assump_246 assump_247 =>
            cases assump_246
            case intro assump_248 assump_249 =>
              cases assump_249
              case inl assump_252 =>
                cases assump_245
                case intro assump_258 assump_259 =>
                  cases assump_258
                  case intro assump_260 assump_261 =>
                    cases assump_260
                    case intro assump_262 assump_263 =>
                      apply False.elim assump_263
              case inr assump_253 =>
                cases assump_245
                case intro assump_272 assump_273 =>
                  cases assump_272
                  case intro assump_274 assump_275 =>
                    cases assump_274
                    case intro assump_276 assump_277 =>
                      apply False.elim assump_277


variable (p4 p2 p7 p5 p6 p3 p0 p1 : Prop)
theorem file100_7651 : (((((p2 → False) → False) → False) ∧ (((p5 ∨ True) ∧ (p4 ∨ p7)) ∧ ((p7 → False) ∧ (p0 ∧ p1)))) → ((((p6 ∨ p4) ∨ (p0 ∧ p3)) → ((p5 → False) ∧ (p7 ∨ True))) → (((p7 ∧ True) → (p4 ∨ p7)) ∨ ((p0 → False) ∧ (p7 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case inl assump_17 =>
            cases assump_10
            case intro assump_21 assump_22 =>
              cases assump_22
              case intro assump_25 assump_26 =>
                apply Or.inl
                intro assump_31
                cases assump_31
                case intro assump_32 assump_33 =>
                  apply Or.inl
                  exact assump_17
          case inr assump_18 =>
            cases assump_10
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                apply Or.inl
                intro assump_50
                cases assump_50
                case intro assump_51 assump_52 =>
                  apply Or.inr
                  exact assump_51
        case inr assump_14 =>
          cases assump_12
          case inl assump_59 =>
            cases assump_10
            case intro assump_63 assump_64 =>
              cases assump_64
              case intro assump_67 assump_68 =>
                apply Or.inl
                intro assump_73
                cases assump_73
                case intro assump_74 assump_75 =>
                  apply Or.inl
                  exact assump_59
          case inr assump_60 =>
            cases assump_10
            case intro assump_82 assump_83 =>
              cases assump_83
              case intro assump_86 assump_87 =>
                apply Or.inl
                intro assump_92
                cases assump_92
                case intro assump_93 assump_94 =>
                  apply Or.inr
                  exact assump_93


variable (p0 p7 p4 p6 p2 p5 p3 : Prop)
theorem file100_9842 : ((((((p4 → False) ∨ (True ∨ p2)) → ((p3 ∨ True) ∨ (p0 ∧ p4))) ∨ (((p5 → p6) → False) ∧ ((True ∧ p7) ∨ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p4 → False) ∨ (True ∨ p2)) → ((p3 ∨ True) ∨ (p0 ∧ p4))) ∨ (((p5 → p6) → False) ∧ ((True ∧ p7) ∨ (p7 → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p3 p7 : Prop)
theorem file100_10635 : (((((p3 → p6) → (False ∧ p3)) → ((False ∧ p7) → False)) → False) → False) := by
  intro assump_9
  have assump_22 : (((p3 → p6) → (False ∧ p3)) → ((False ∧ p7) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_15
  let assump_12 := assump_9 assump_22
  apply False.elim assump_12


variable (p2 p6 p1 p3 p5 p7 p4 p0 : Prop)
theorem file100_11075 : (((((p4 ∧ p4) ∨ (p0 ∨ p3)) → False) ∨ (((p2 → False) → (p6 ∨ p2)) ∨ ((True ∧ False) ∧ (p5 → p4)))) → ((((p2 ∧ False) ∧ (p7 → False)) ∧ ((p2 → p5) ∨ (p6 → False))) → (((p4 ∧ True) ∨ (p5 ∧ p6)) ∨ ((p1 → False) ∧ (p6 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p3 p5 p1 p0 p4 p7 p2 p6 : Prop)
theorem file100_11607 : (((((p2 ∧ p4) ∨ (True ∧ True)) ∧ ((p3 ∧ True) → False)) → (((p7 → p7) → False) → ((p7 ∧ p6) ∨ (p1 → p5)))) ∨ ((((p0 → False) → (p4 ∨ p6)) → False) → (((p2 → p3) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inr
        intro assump_17
        have assump_51 : (p7 → p7) := by
          intro assump_25
          exact assump_25
        let assump_24 := assump_2 assump_51
        apply False.elim assump_24
    case inr assump_8 =>
      cases assump_8
      case intro assump_31 assump_32 =>
        apply Or.inr
        intro assump_39
        have assump_52 : (p7 → p7) := by
          intro assump_45
          exact assump_45
        let assump_44 := assump_2 assump_52
        apply False.elim assump_44


variable (p4 p0 p2 p5 p7 p6 : Prop)
theorem file100_12578 : ((((((True → False) ∧ (p2 ∨ p2)) ∨ ((p0 → False) → (p2 → False))) → (((p4 → p7) → False) → ((p6 ∨ True) ∨ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((True → False) ∧ (p2 ∨ p2)) ∨ ((p0 → False) → (p2 → False))) → (((p4 → p7) → False) → ((p6 ∨ True) ∨ (p5 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_16 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p1 p2 p0 p6 p7 : Prop)
theorem file100_13471 : ((((((False → p5) ∧ (p7 ∧ p7)) → False) → (((p7 → p6) ∨ (p1 ∨ p0)) ∧ ((p2 ∧ p0) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((False → p5) ∧ (p7 ∧ p7)) → False) → (((p7 → p6) ∨ (p1 ∨ p0)) ∧ ((p2 ∧ p0) → (False → False)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_27 : ((False → p5) ∧ (p7 ∧ p7)) := by
      apply And.intro
      intro assump_13
      apply False.elim assump_13
      apply And.intro
      exact assump_8
      exact assump_8
    let assump_12 := assump_5 assump_27
    apply False.elim assump_12
    intro assump_19
    intro assump_20
    apply False.elim assump_20
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p0 p5 p2 p3 p7 p4 p1 : Prop)
theorem file100_14277 : (((((p4 ∨ p5) ∧ (p4 → False)) → False) → (((False ∨ p4) ∨ (False → False)) → False)) → ((((p7 ∨ False) ∧ (p2 ∧ p1)) → ((p2 ∨ p7) ∧ (p2 ∧ p2))) ∨ (((p0 → p3) → (p4 → False)) → ((True ∨ p7) ∧ (p0 ∨ p2))))) := by
  intro assump_39
  apply Or.inl
  intro assump_42
  apply And.intro
  cases assump_42
  case intro assump_43 assump_44 =>
    cases assump_43
    case inl assump_45 =>
      cases assump_44
      case intro assump_49 assump_50 =>
        apply Or.inl
        exact assump_49
    case inr assump_46 =>
      apply False.elim assump_46
  apply And.intro
  cases assump_42
  case intro assump_57 assump_58 =>
    cases assump_57
    case inl assump_59 =>
      cases assump_58
      case intro assump_63 assump_64 =>
        exact assump_63
    case inr assump_60 =>
      apply False.elim assump_60
  cases assump_42
  case intro assump_71 assump_72 =>
    cases assump_71
    case inl assump_73 =>
      cases assump_72
      case intro assump_77 assump_78 =>
        exact assump_77
    case inr assump_74 =>
      apply False.elim assump_74


variable (p4 p6 p1 p7 p5 p0 p3 : Prop)
theorem file100_15393 : ((((((p0 ∧ p7) ∧ (False ∧ p5)) → False) ∨ (((p4 ∧ p6) ∨ (p4 → p3)) ∧ ((p0 → p1) ∨ (p5 → p3)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 ∧ p7) ∧ (False ∧ p5)) → False) ∨ (((p4 ∧ p6) ∨ (p4 → p3)) ∧ ((p0 → p1) ∨ (p5 → p3)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p3 p1 p4 p2 p7 p0 : Prop)
theorem file100_16027 : ((((((True → p3) → False) ∨ ((p7 ∧ False) ∨ (p2 → False))) → (((p7 → True) ∨ (p0 → p7)) ∧ ((p2 → False) → False))) ∧ ((((p0 ∧ False) → (p6 ∧ p2)) → False) ∧ (((p0 → p1) → (p6 → True)) ∧ ((p4 → False) ∧ (p3 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            have assump_30 : p4 := by
              exact assump_19
            let assump_26 := assump_14 assump_30
            apply False.elim assump_26


variable (p2 p7 p6 p3 p4 p5 p0 : Prop)
theorem file100_16797 : (((((False ∧ p6) ∨ (False ∧ p6)) ∧ ((False ∧ p2) ∨ (p2 → p7))) ∧ (((p7 → False) → (p6 ∨ p6)) → ((True → False) ∨ (p3 → False)))) → ((((p2 ∨ False) → False) → False) → (((p5 → p0) ∨ (p2 → p4)) → ((True ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case inl assump_11 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              apply False.elim assump_23
          case inr assump_22 =>
            cases assump_22
            case intro assump_27 assump_28 =>
              apply False.elim assump_27
    case inr assump_12 =>
      cases assump_1
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_37
          case inl assump_39 =>
            cases assump_39
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
          case inr assump_40 =>
            cases assump_40
            case intro assump_45 assump_46 =>
              apply False.elim assump_45


variable (p4 p3 p2 p7 p6 : Prop)
theorem file100_18163 : ((((((p3 ∨ p6) → False) → ((p6 → False) → False)) → (((p4 ∧ p7) ∨ (False ∨ True)) → ((p7 ∧ p7) → (p2 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p3 ∨ p6) → False) → ((p6 → False) → False)) → (((p4 ∧ p7) ∨ (False ∨ True)) → ((p7 ∧ p7) → (p2 ∨ p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inr
          exact assump_17
      case inr assump_15 =>
        cases assump_15
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          apply Or.inr
          exact assump_9
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p0 p6 p7 p5 p3 p4 p2 : Prop)
theorem file100_19048 : (((((p2 ∨ p7) ∧ (p4 → p2)) ∧ ((p7 → False) → False)) ∧ (((p5 ∧ p6) ∧ (False ∧ True)) → False)) → ((((False ∧ p2) ∧ (p0 → False)) ∧ ((p4 ∨ p5) → (False ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p3 p0 p5 p2 p4 p1 p6 : Prop)
theorem file100_19519 : (((((p0 ∨ p2) → (p0 ∧ p6)) ∨ ((True → p3) ∧ (p3 → False))) → (((True ∨ p2) ∨ (p6 ∧ p2)) ∨ ((p0 ∨ p6) → (p5 → p1)))) ∨ ((((False → False) → (True ∧ p4)) ∧ ((p6 → p4) → (p5 → p2))) ∧ (((p3 ∧ p2) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p0 p2 p5 p4 p3 p1 p7 p6 : Prop)
theorem file100_20106 : (((((False → False) → (False ∧ p3)) → False) ∨ (((p1 ∨ p5) ∨ (p2 ∧ p1)) → ((False → True) ∧ (p7 → False)))) ∨ ((((False ∧ p6) ∧ (False → False)) → ((p4 ∧ p2) → (p6 → p7))) ∨ (((p0 → p2) ∧ (p3 ∧ p6)) → ((p0 ∨ p3) → (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_12 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_12
  let assump_8 := And.left assump_4
  apply False.elim assump_8


variable (p7 p0 p4 p6 p3 : Prop)
theorem file100_20638 : ((((((p0 ∨ True) → False) → False) ∨ (((p0 ∨ p4) ∧ (p7 ∧ False)) ∨ ((p6 → p3) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p0 ∨ True) → False) → False) ∨ (((p0 ∨ p4) ∧ (p7 ∧ False)) ∨ ((p6 → p3) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p0 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p3 p0 p6 : Prop)
theorem file100_21185 : (((((p0 ∧ False) ∧ (p6 ∧ False)) → ((p3 → False) ∨ (p6 → p7))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p0 ∧ False) ∧ (p6 ∧ False)) → ((p3 → False) ∨ (p6 → p7))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p1 p5 p0 p2 p6 : Prop)
theorem file100_21667 : ((((((p6 → p6) ∨ (p5 → p4)) ∨ ((p2 → False) → (p0 → False))) ∨ (((p6 → False) ∧ (p6 ∧ p0)) → False)) ∧ ((((p1 ∨ False) ∧ (p0 ∧ p2)) → ((p1 ∧ p0) ∨ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_102 : (((p1 ∨ False) ∧ (p0 ∧ p2)) → ((p1 ∧ p0) ∨ (p5 → False))) := by
            intro assump_15
            cases assump_15
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_17
                case intro assump_22 assump_23 =>
                  apply Or.inl
                  apply And.intro
                  exact assump_18
                  exact assump_22
              case inr assump_19 =>
                apply False.elim assump_19
          let assump_14 := assump_3 assump_102
          apply False.elim assump_14
        case inr assump_9 =>
          have assump_103 : (((p1 ∨ False) ∧ (p0 ∧ p2)) → ((p1 ∧ p0) ∨ (p5 → False))) := by
            intro assump_38
            cases assump_38
            case intro assump_39 assump_40 =>
              cases assump_39
              case inl assump_41 =>
                cases assump_40
                case intro assump_45 assump_46 =>
                  apply Or.inl
                  apply And.intro
                  exact assump_41
                  exact assump_45
              case inr assump_42 =>
                apply False.elim assump_42
          let assump_37 := assump_3 assump_103
          apply False.elim assump_37
      case inr assump_7 =>
        have assump_104 : (((p1 ∨ False) ∧ (p0 ∧ p2)) → ((p1 ∧ p0) ∨ (p5 → False))) := by
          intro assump_61
          cases assump_61
          case intro assump_62 assump_63 =>
            cases assump_62
            case inl assump_64 =>
              cases assump_63
              case intro assump_68 assump_69 =>
                apply Or.inl
                apply And.intro
                exact assump_64
                exact assump_68
            case inr assump_65 =>
              apply False.elim assump_65
        let assump_60 := assump_3 assump_104
        apply False.elim assump_60
    case inr assump_5 =>
      have assump_105 : (((p1 ∨ False) ∧ (p0 ∧ p2)) → ((p1 ∧ p0) ∨ (p5 → False))) := by
        intro assump_84
        cases assump_84
        case intro assump_85 assump_86 =>
          cases assump_85
          case inl assump_87 =>
            cases assump_86
            case intro assump_91 assump_92 =>
              apply Or.inl
              apply And.intro
              exact assump_87
              exact assump_91
          case inr assump_88 =>
            apply False.elim assump_88
      let assump_83 := assump_3 assump_105
      apply False.elim assump_83


variable (p1 p3 p2 p7 p0 p4 : Prop)
theorem file100_24663 : ((((((p0 ∧ p0) ∧ (p7 → True)) ∨ ((p2 ∨ p1) ∨ (p3 ∧ p2))) ∨ (((p4 ∧ p2) ∧ (p0 → False)) → ((p2 → False) → (p3 ∨ p0)))) → False) → False) := by
  intro assump_29
  have assump_57 : ((((p0 ∧ p0) ∧ (p7 → True)) ∨ ((p2 ∨ p1) ∨ (p3 ∧ p2))) ∨ (((p4 ∧ p2) ∧ (p0 → False)) → ((p2 → False) → (p3 ∨ p0)))) := by
    apply Or.inr
    intro assump_33
    intro assump_34
    cases assump_33
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        have assump_58 : p2 := by
          exact assump_40
        let assump_50 := assump_34 assump_58
        apply False.elim assump_50
  let assump_32 := assump_29 assump_57
  apply False.elim assump_32


variable (p0 p2 p3 p5 p7 p6 p4 : Prop)
theorem file100_25412 : (((((p4 ∧ False) ∧ (p5 → False)) → False) ∨ (((p3 → False) → False) ∨ ((p0 ∧ p2) → False))) ∨ ((((p7 ∨ p6) ∨ (p3 → p0)) ∨ ((p3 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5


variable (p6 p1 p3 p2 p0 p7 p4 : Prop)
theorem file100_25822 : (((((p0 ∨ False) → (p6 ∨ p0)) ∨ ((True → p1) → (p4 ∨ p4))) ∨ (((p7 ∧ p1) → False) ∧ ((p1 → p6) → False))) ∨ ((((True → False) ∨ (p2 ∨ p7)) ∧ ((p7 ∨ p2) → False)) ∨ (((False → False) ∧ (p3 ∨ True)) ∨ ((False ∧ p3) ∧ (p7 ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    exact assump_2
  case inr assump_3 =>
    apply False.elim assump_3


variable (p5 p2 p6 p1 p4 p7 p3 p0 : Prop)
theorem file100_26317 : (((((False → p7) → False) ∧ ((p6 ∨ p4) → (p4 → False))) ∧ (((p3 → p2) → (True → False)) ∨ ((p5 ∨ p1) ∨ (p0 → False)))) → ((((p7 → p1) → False) ∧ ((p5 → False) → False)) → (((p1 ∧ False) ∧ (p6 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p3 p2 p5 p4 p0 p1 : Prop)
theorem file100_26785 : ((((((p0 → False) → (p1 ∨ p3)) → ((p4 ∨ p5) → (False → False))) ∨ (((p4 → False) → (False ∨ True)) ∧ ((False ∨ p4) ∧ (p2 → False)))) → False) → False) := by
  intro assump_47
  have assump_59 : ((((p0 → False) → (p1 ∨ p3)) → ((p4 ∨ p5) → (False → False))) ∨ (((p4 → False) → (False ∨ True)) ∧ ((False ∨ p4) ∧ (p2 → False)))) := by
    apply Or.inl
    intro assump_51
    intro assump_52
    intro assump_53
    apply False.elim assump_53
  let assump_50 := assump_47 assump_59
  apply False.elim assump_50


variable (p4 p1 p6 p5 p7 p0 p2 : Prop)
theorem file100_27355 : (((((p6 ∨ p5) ∧ (p0 ∧ False)) → ((p2 ∧ p6) ∨ (True ∨ False))) ∨ (((p7 → True) ∨ (False ∨ True)) → False)) ∧ ((((True → True) ∧ (p5 ∨ False)) → ((p4 ∧ False) → False)) ∨ (((p1 → p5) → False) ∨ ((p1 ∨ True) ∧ (p0 → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
  apply Or.inl
  intro assump_22
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    apply False.elim assump_25


variable (p3 p6 p5 p0 : Prop)
theorem file100_28134 : (((((True ∨ p6) → False) → False) ∨ (((True ∧ p0) ∧ (p5 ∧ False)) → False)) ∨ ((((p5 → p0) ∧ (p5 ∧ False)) ∨ ((p3 → False) ∨ (p6 → p5))) ∧ (((p6 → p5) ∧ (p0 ∨ False)) → ((p0 ∧ False) ∧ (True → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (True ∨ p6) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p5 p1 p2 p0 p7 : Prop)
theorem file100_28589 : (((((p1 → p3) ∧ (True ∨ p1)) ∧ ((p2 → False) → (p5 ∨ p7))) ∧ (((False → p5) ∨ (p3 → False)) → False)) → ((((p0 ∧ p0) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case inl assump_13 =>
          have assump_41 : ((False → p5) ∨ (p3 → False)) := by
            apply Or.inl
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_6 assump_41
          apply False.elim assump_21
        case inr assump_14 =>
          have assump_42 : ((False → p5) ∨ (p3 → False)) := by
            apply Or.inl
            intro assump_35
            apply False.elim assump_35
          let assump_34 := assump_6 assump_42
          apply False.elim assump_34


variable (p0 p3 p5 p2 p7 : Prop)
theorem file100_29557 : (((((p3 → False) → (False ∨ p7)) ∧ ((p0 ∧ p5) ∨ (False ∨ p2))) ∧ (((False → False) → False) ∧ ((p0 → p3) ∧ (True ∨ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                have assump_87 : (False → False) := by
                  intro assump_31
                  apply False.elim assump_31
                let assump_30 := assump_16 assump_87
                apply False.elim assump_30
              case inr assump_25 =>
                have assump_88 : (False → False) := by
                  intro assump_43
                  apply False.elim assump_43
                let assump_42 := assump_16 assump_88
                apply False.elim assump_42
      case inr assump_9 =>
        cases assump_9
        case inl assump_49 =>
          apply False.elim assump_49
        case inr assump_50 =>
          cases assump_3
          case intro assump_55 assump_56 =>
            cases assump_56
            case intro assump_59 assump_60 =>
              cases assump_60
              case inl assump_63 =>
                have assump_89 : (False → False) := by
                  intro assump_69
                  apply False.elim assump_69
                let assump_68 := assump_55 assump_89
                apply False.elim assump_68
              case inr assump_64 =>
                have assump_90 : (False → False) := by
                  intro assump_81
                  apply False.elim assump_81
                let assump_80 := assump_55 assump_90
                apply False.elim assump_80


variable (p5 p4 p0 p3 p1 : Prop)
theorem file100_31544 : ((((((False → p3) ∧ (False ∧ p5)) → ((True → p4) ∧ (p5 → p5))) ∨ (((p1 ∧ p5) ∧ (p4 ∨ p5)) ∨ ((p0 ∨ p4) ∧ (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((False → p3) ∧ (False ∧ p5)) → ((True → p4) ∧ (p5 → p5))) ∨ (((p1 ∧ p5) ∧ (p4 ∨ p5)) ∨ ((p0 ∨ p4) ∧ (False → p1)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    intro assump_17
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p1 p0 p2 p4 : Prop)
theorem file100_32371 : ((((((p1 ∧ True) → False) → ((p4 ∧ False) → (p4 → False))) ∨ (((p0 → False) ∧ (p2 → False)) ∨ ((p2 ∨ True) ∧ (False ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p1 ∧ True) → False) → ((p4 ∧ False) → (p4 → False))) ∨ (((p0 → False) ∧ (p2 → False)) ∨ ((p2 ∨ True) ∧ (False ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p3 p7 p0 p4 p2 : Prop)
theorem file100_32974 : ((((((p2 ∨ True) → (False ∨ True)) ∨ ((p1 ∨ p7) ∨ (False → False))) ∧ (((p4 → True) ∨ (p3 ∧ p0)) ∨ ((p7 ∧ p4) ∧ (True ∧ p4)))) ∧ ((((p3 ∧ True) → (p1 → p0)) → False) ∧ (((p7 → p0) ∨ (p1 → p0)) ∧ ((p1 ∧ p0) ∧ (p1 → p3))))) → False) := by
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
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_21
                  case intro assump_26 assump_27 =>
                    cases assump_26
                    case intro assump_28 assump_29 =>
                      have assump_982 : ((p3 ∧ True) → (p1 → p0)) := by
                        intro assump_42
                        intro assump_43
                        cases assump_42
                        case intro assump_46 assump_47 =>
                          exact assump_29
                      let assump_41 := assump_16 assump_982
                      apply False.elim assump_41
                case inr assump_23 =>
                  cases assump_21
                  case intro assump_57 assump_58 =>
                    cases assump_57
                    case intro assump_59 assump_60 =>
                      have assump_983 : ((p3 ∧ True) → (p1 → p0)) := by
                        intro assump_74
                        intro assump_75
                        cases assump_74
                        case intro assump_78 assump_79 =>
                          exact assump_60
                      let assump_73 := assump_16 assump_983
                      apply False.elim assump_73
          case inr assump_13 =>
            cases assump_13
            case intro assump_87 assump_88 =>
              cases assump_3
              case intro assump_93 assump_94 =>
                cases assump_94
                case intro assump_97 assump_98 =>
                  cases assump_97
                  case inl assump_99 =>
                    cases assump_98
                    case intro assump_103 assump_104 =>
                      cases assump_103
                      case intro assump_105 assump_106 =>
                        have assump_984 : ((p3 ∧ True) → (p1 → p0)) := by
                          intro assump_119
                          intro assump_120
                          cases assump_119
                          case intro assump_123 assump_124 =>
                            exact assump_106
                        let assump_118 := assump_93 assump_984
                        apply False.elim assump_118
                  case inr assump_100 =>
                    cases assump_98
                    case intro assump_134 assump_135 =>
                      cases assump_134
                      case intro assump_136 assump_137 =>
                        have assump_985 : ((p3 ∧ True) → (p1 → p0)) := by
                          intro assump_151
                          intro assump_152
                          cases assump_151
                          case intro assump_155 assump_156 =>
                            exact assump_137
                        let assump_150 := assump_93 assump_985
                        apply False.elim assump_150
        case inr assump_11 =>
          cases assump_11
          case intro assump_164 assump_165 =>
            cases assump_164
            case intro assump_166 assump_167 =>
              cases assump_165
              case intro assump_172 assump_173 =>
                cases assump_3
                case intro assump_178 assump_179 =>
                  cases assump_179
                  case intro assump_182 assump_183 =>
                    cases assump_182
                    case inl assump_184 =>
                      cases assump_183
                      case intro assump_188 assump_189 =>
                        cases assump_188
                        case intro assump_190 assump_191 =>
                          have assump_986 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_205
                            intro assump_206
                            cases assump_205
                            case intro assump_209 assump_210 =>
                              exact assump_191
                          let assump_204 := assump_178 assump_986
                          apply False.elim assump_204
                    case inr assump_185 =>
                      cases assump_183
                      case intro assump_220 assump_221 =>
                        cases assump_220
                        case intro assump_222 assump_223 =>
                          have assump_987 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_237
                            intro assump_238
                            cases assump_237
                            case intro assump_241 assump_242 =>
                              exact assump_223
                          let assump_236 := assump_178 assump_987
                          apply False.elim assump_236
      case inr assump_7 =>
        cases assump_7
        case inl assump_250 =>
          cases assump_250
          case inl assump_252 =>
            cases assump_5
            case inl assump_256 =>
              cases assump_256
              case inl assump_258 =>
                cases assump_3
                case intro assump_262 assump_263 =>
                  cases assump_263
                  case intro assump_266 assump_267 =>
                    cases assump_266
                    case inl assump_268 =>
                      cases assump_267
                      case intro assump_272 assump_273 =>
                        cases assump_272
                        case intro assump_274 assump_275 =>
                          have assump_988 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_288
                            intro assump_289
                            cases assump_288
                            case intro assump_292 assump_293 =>
                              exact assump_275
                          let assump_287 := assump_262 assump_988
                          apply False.elim assump_287
                    case inr assump_269 =>
                      cases assump_267
                      case intro assump_303 assump_304 =>
                        cases assump_303
                        case intro assump_305 assump_306 =>
                          have assump_989 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_320
                            intro assump_321
                            cases assump_320
                            case intro assump_324 assump_325 =>
                              exact assump_306
                          let assump_319 := assump_262 assump_989
                          apply False.elim assump_319
              case inr assump_259 =>
                cases assump_259
                case intro assump_333 assump_334 =>
                  cases assump_3
                  case intro assump_339 assump_340 =>
                    cases assump_340
                    case intro assump_343 assump_344 =>
                      cases assump_343
                      case inl assump_345 =>
                        cases assump_344
                        case intro assump_349 assump_350 =>
                          cases assump_349
                          case intro assump_351 assump_352 =>
                            have assump_990 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_365
                              intro assump_366
                              cases assump_365
                              case intro assump_369 assump_370 =>
                                exact assump_352
                            let assump_364 := assump_339 assump_990
                            apply False.elim assump_364
                      case inr assump_346 =>
                        cases assump_344
                        case intro assump_380 assump_381 =>
                          cases assump_380
                          case intro assump_382 assump_383 =>
                            have assump_991 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_397
                              intro assump_398
                              cases assump_397
                              case intro assump_401 assump_402 =>
                                exact assump_383
                            let assump_396 := assump_339 assump_991
                            apply False.elim assump_396
            case inr assump_257 =>
              cases assump_257
              case intro assump_410 assump_411 =>
                cases assump_410
                case intro assump_412 assump_413 =>
                  cases assump_411
                  case intro assump_418 assump_419 =>
                    cases assump_3
                    case intro assump_424 assump_425 =>
                      cases assump_425
                      case intro assump_428 assump_429 =>
                        cases assump_428
                        case inl assump_430 =>
                          cases assump_429
                          case intro assump_434 assump_435 =>
                            cases assump_434
                            case intro assump_436 assump_437 =>
                              have assump_992 : ((p3 ∧ True) → (p1 → p0)) := by
                                intro assump_451
                                intro assump_452
                                cases assump_451
                                case intro assump_455 assump_456 =>
                                  exact assump_437
                              let assump_450 := assump_424 assump_992
                              apply False.elim assump_450
                        case inr assump_431 =>
                          cases assump_429
                          case intro assump_466 assump_467 =>
                            cases assump_466
                            case intro assump_468 assump_469 =>
                              have assump_993 : ((p3 ∧ True) → (p1 → p0)) := by
                                intro assump_483
                                intro assump_484
                                cases assump_483
                                case intro assump_487 assump_488 =>
                                  exact assump_469
                              let assump_482 := assump_424 assump_993
                              apply False.elim assump_482
          case inr assump_253 =>
            cases assump_5
            case inl assump_498 =>
              cases assump_498
              case inl assump_500 =>
                cases assump_3
                case intro assump_504 assump_505 =>
                  cases assump_505
                  case intro assump_508 assump_509 =>
                    cases assump_508
                    case inl assump_510 =>
                      cases assump_509
                      case intro assump_514 assump_515 =>
                        cases assump_514
                        case intro assump_516 assump_517 =>
                          have assump_994 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_531
                            intro assump_532
                            cases assump_531
                            case intro assump_535 assump_536 =>
                              exact assump_517
                          let assump_530 := assump_504 assump_994
                          apply False.elim assump_530
                    case inr assump_511 =>
                      cases assump_509
                      case intro assump_546 assump_547 =>
                        cases assump_546
                        case intro assump_548 assump_549 =>
                          have assump_995 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_563
                            intro assump_564
                            cases assump_563
                            case intro assump_567 assump_568 =>
                              exact assump_549
                          let assump_562 := assump_504 assump_995
                          apply False.elim assump_562
              case inr assump_501 =>
                cases assump_501
                case intro assump_576 assump_577 =>
                  cases assump_3
                  case intro assump_582 assump_583 =>
                    cases assump_583
                    case intro assump_586 assump_587 =>
                      cases assump_586
                      case inl assump_588 =>
                        cases assump_587
                        case intro assump_592 assump_593 =>
                          cases assump_592
                          case intro assump_594 assump_595 =>
                            have assump_996 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_609
                              intro assump_610
                              cases assump_609
                              case intro assump_613 assump_614 =>
                                exact assump_595
                            let assump_608 := assump_582 assump_996
                            apply False.elim assump_608
                      case inr assump_589 =>
                        cases assump_587
                        case intro assump_624 assump_625 =>
                          cases assump_624
                          case intro assump_626 assump_627 =>
                            have assump_997 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_641
                              intro assump_642
                              cases assump_641
                              case intro assump_645 assump_646 =>
                                exact assump_627
                            let assump_640 := assump_582 assump_997
                            apply False.elim assump_640
            case inr assump_499 =>
              cases assump_499
              case intro assump_654 assump_655 =>
                cases assump_654
                case intro assump_656 assump_657 =>
                  cases assump_655
                  case intro assump_662 assump_663 =>
                    cases assump_3
                    case intro assump_668 assump_669 =>
                      cases assump_669
                      case intro assump_672 assump_673 =>
                        cases assump_672
                        case inl assump_674 =>
                          cases assump_673
                          case intro assump_678 assump_679 =>
                            cases assump_678
                            case intro assump_680 assump_681 =>
                              have assump_998 : ((p3 ∧ True) → (p1 → p0)) := by
                                intro assump_695
                                intro assump_696
                                cases assump_695
                                case intro assump_699 assump_700 =>
                                  exact assump_681
                              let assump_694 := assump_668 assump_998
                              apply False.elim assump_694
                        case inr assump_675 =>
                          cases assump_673
                          case intro assump_710 assump_711 =>
                            cases assump_710
                            case intro assump_712 assump_713 =>
                              have assump_999 : ((p3 ∧ True) → (p1 → p0)) := by
                                intro assump_727
                                intro assump_728
                                cases assump_727
                                case intro assump_731 assump_732 =>
                                  exact assump_713
                              let assump_726 := assump_668 assump_999
                              apply False.elim assump_726
        case inr assump_251 =>
          cases assump_5
          case inl assump_742 =>
            cases assump_742
            case inl assump_744 =>
              cases assump_3
              case intro assump_748 assump_749 =>
                cases assump_749
                case intro assump_752 assump_753 =>
                  cases assump_752
                  case inl assump_754 =>
                    cases assump_753
                    case intro assump_758 assump_759 =>
                      cases assump_758
                      case intro assump_760 assump_761 =>
                        have assump_1000 : ((p3 ∧ True) → (p1 → p0)) := by
                          intro assump_774
                          intro assump_775
                          cases assump_774
                          case intro assump_778 assump_779 =>
                            exact assump_761
                        let assump_773 := assump_748 assump_1000
                        apply False.elim assump_773
                  case inr assump_755 =>
                    cases assump_753
                    case intro assump_789 assump_790 =>
                      cases assump_789
                      case intro assump_791 assump_792 =>
                        have assump_1001 : ((p3 ∧ True) → (p1 → p0)) := by
                          intro assump_806
                          intro assump_807
                          cases assump_806
                          case intro assump_810 assump_811 =>
                            exact assump_792
                        let assump_805 := assump_748 assump_1001
                        apply False.elim assump_805
            case inr assump_745 =>
              cases assump_745
              case intro assump_819 assump_820 =>
                cases assump_3
                case intro assump_825 assump_826 =>
                  cases assump_826
                  case intro assump_829 assump_830 =>
                    cases assump_829
                    case inl assump_831 =>
                      cases assump_830
                      case intro assump_835 assump_836 =>
                        cases assump_835
                        case intro assump_837 assump_838 =>
                          have assump_1002 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_851
                            intro assump_852
                            cases assump_851
                            case intro assump_855 assump_856 =>
                              exact assump_838
                          let assump_850 := assump_825 assump_1002
                          apply False.elim assump_850
                    case inr assump_832 =>
                      cases assump_830
                      case intro assump_866 assump_867 =>
                        cases assump_866
                        case intro assump_868 assump_869 =>
                          have assump_1003 : ((p3 ∧ True) → (p1 → p0)) := by
                            intro assump_883
                            intro assump_884
                            cases assump_883
                            case intro assump_887 assump_888 =>
                              exact assump_869
                          let assump_882 := assump_825 assump_1003
                          apply False.elim assump_882
          case inr assump_743 =>
            cases assump_743
            case intro assump_896 assump_897 =>
              cases assump_896
              case intro assump_898 assump_899 =>
                cases assump_897
                case intro assump_904 assump_905 =>
                  cases assump_3
                  case intro assump_910 assump_911 =>
                    cases assump_911
                    case intro assump_914 assump_915 =>
                      cases assump_914
                      case inl assump_916 =>
                        cases assump_915
                        case intro assump_920 assump_921 =>
                          cases assump_920
                          case intro assump_922 assump_923 =>
                            have assump_1004 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_937
                              intro assump_938
                              cases assump_937
                              case intro assump_941 assump_942 =>
                                exact assump_923
                            let assump_936 := assump_910 assump_1004
                            apply False.elim assump_936
                      case inr assump_917 =>
                        cases assump_915
                        case intro assump_952 assump_953 =>
                          cases assump_952
                          case intro assump_954 assump_955 =>
                            have assump_1005 : ((p3 ∧ True) → (p1 → p0)) := by
                              intro assump_969
                              intro assump_970
                              cases assump_969
                              case intro assump_973 assump_974 =>
                                exact assump_955
                            let assump_968 := assump_910 assump_1005
                            apply False.elim assump_968


variable (p2 p7 p1 p5 p4 p0 : Prop)
theorem file100_54771 : ((((((False ∧ True) → False) ∨ ((p7 → p1) → (p0 → False))) → False) ∧ ((((p2 ∨ p1) ∧ (p7 ∧ p1)) ∧ ((p4 ∧ p0) → (False → False))) → (((True → False) → False) → ((p1 ∨ p5) → (p7 ∨ p4))))) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    have assump_41 : (((False ∧ True) → False) ∨ ((p7 → p1) → (p0 → False))) := by
      apply Or.inl
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        apply False.elim assump_34
    let assump_32 := assump_25 assump_41
    apply False.elim assump_32


variable (p5 p2 p6 p4 p0 p7 : Prop)
theorem file100_55397 : ((((((p7 ∨ p6) ∧ (p7 → False)) ∨ ((p2 ∨ p5) ∨ (p5 → False))) ∧ (((p0 ∨ p7) ∧ (p2 → False)) → ((p4 ∨ True) → (p2 → p5)))) → False) → False) := by
  intro assump_1
  have assump_102 : ((((p7 ∨ p6) ∧ (p7 → False)) ∨ ((p2 ∨ p5) ∨ (p5 → False))) ∧ (((p0 ∨ p7) ∧ (p2 → False)) → ((p4 ∨ True) → (p2 → p5)))) := by
    apply And.intro
    apply Or.inr
    apply Or.inr
    intro assump_5
    have assump_103 : ((((p7 ∨ p6) ∧ (p7 → False)) ∨ ((p2 ∨ p5) ∨ (p5 → False))) ∧ (((p0 ∨ p7) ∧ (p2 → False)) → ((p4 ∨ True) → (p2 → p5)))) := by
      apply And.intro
      apply Or.inr
      apply Or.inl
      apply Or.inr
      exact assump_5
      intro assump_10
      intro assump_11
      intro assump_12
      cases assump_11
      case inl assump_15 =>
        cases assump_10
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            exact assump_5
          case inr assump_22 =>
            exact assump_5
      case inr assump_16 =>
        cases assump_10
        case intro assump_33 assump_34 =>
          cases assump_33
          case inl assump_35 =>
            exact assump_5
          case inr assump_36 =>
            exact assump_5
    let assump_9 := assump_1 assump_103
    apply False.elim assump_9
    intro assump_48
    intro assump_49
    intro assump_50
    cases assump_49
    case inl assump_53 =>
      cases assump_48
      case intro assump_57 assump_58 =>
        cases assump_57
        case inl assump_59 =>
          have assump_104 : p2 := by
            exact assump_50
          let assump_65 := assump_58 assump_104
          apply False.elim assump_65
        case inr assump_60 =>
          have assump_105 : p2 := by
            exact assump_50
          let assump_73 := assump_58 assump_105
          apply False.elim assump_73
    case inr assump_54 =>
      cases assump_48
      case intro assump_79 assump_80 =>
        cases assump_79
        case inl assump_81 =>
          have assump_106 : p2 := by
            exact assump_50
          let assump_87 := assump_80 assump_106
          apply False.elim assump_87
        case inr assump_82 =>
          have assump_107 : p2 := by
            exact assump_50
          let assump_95 := assump_80 assump_107
          apply False.elim assump_95
  let assump_4 := assump_1 assump_102
  apply False.elim assump_4


variable (p4 p2 p7 p0 p6 p3 p5 p1 : Prop)
theorem file100_57814 : (((((p7 ∧ p7) → (p0 → p2)) ∨ ((p2 ∧ p7) ∧ (p6 ∧ p4))) → False) → ((((p1 ∧ p6) ∧ (p5 → False)) → ((False ∨ p6) ∧ (p6 ∨ p5))) ∨ (((p1 → False) → (p3 ∨ True)) → False))) := by
  intro assump_28
  apply Or.inl
  intro assump_31
  apply And.intro
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_32
    case intro assump_34 assump_35 =>
      apply Or.inr
      exact assump_35
  cases assump_31
  case intro assump_42 assump_43 =>
    cases assump_42
    case intro assump_44 assump_45 =>
      apply Or.inl
      exact assump_45


variable (p6 p4 p7 p3 p2 p1 : Prop)
theorem file100_58422 : (((((p4 ∨ False) ∨ (True → p7)) → ((True → False) ∧ (False ∧ p3))) → (((p2 ∨ True) ∧ (p2 → False)) ∧ ((p3 → p6) ∨ (p2 ∨ p1)))) → ((((p4 ∨ p2) ∨ (True ∨ p1)) → False) → (((True → p1) ∧ (p2 → False)) → ((p2 ∧ p4) → (True ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      apply Or.inl
      apply True.intro


variable (p1 p4 p5 p0 p6 p7 p3 : Prop)
theorem file100_58938 : ((((((p4 ∨ p4) ∨ (p6 → p0)) ∧ ((p5 ∧ p0) → False)) → (((p0 → False) ∧ (p7 ∨ p6)) → False)) ∧ ((((p6 → p7) ∨ (True → False)) ∨ ((p0 → p5) → (p1 ∧ p7))) ∧ (((False ∨ p3) → False) ∧ ((p5 → False) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_60 : True := by
                apply True.intro
              let assump_24 := assump_19 assump_60
              apply False.elim assump_24
        case inr assump_11 =>
          cases assump_7
          case intro assump_30 assump_31 =>
            cases assump_31
            case intro assump_34 assump_35 =>
              have assump_61 : True := by
                apply True.intro
              let assump_40 := assump_35 assump_61
              apply False.elim assump_40
      case inr assump_9 =>
        cases assump_7
        case intro assump_46 assump_47 =>
          cases assump_47
          case intro assump_50 assump_51 =>
            have assump_62 : True := by
              apply True.intro
            let assump_56 := assump_51 assump_62
            apply False.elim assump_56


variable (p1 p7 p4 p3 p0 : Prop)
theorem file100_60419 : ((((((p1 → False) → (p0 → False)) ∧ ((p4 → p4) → False)) → (((p7 ∨ p7) ∨ (p3 ∧ p3)) ∨ ((False → p7) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 → False) → (p0 → False)) ∧ ((p4 → p4) → False)) → (((p7 ∨ p7) ∨ (p3 ∧ p3)) ∨ ((False → p7) → (True → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      intro assump_13
      have assump_30 : (p4 → p4) := by
        intro assump_20
        exact assump_20
      let assump_19 := assump_7 assump_30
      apply False.elim assump_19
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p0 p4 p1 p3 p6 p2 p5 : Prop)
theorem file100_61150 : (((((p4 ∧ p2) → False) → ((p3 ∧ p0) → (False → p4))) ∨ (((p2 → False) → False) ∧ ((p2 → False) ∧ (p0 ∧ p1)))) ∨ ((((p6 ∨ p4) ∧ (False ∧ p1)) → False) ∨ (((p2 ∧ p4) → False) → ((p5 ∧ p3) ∨ (p5 ∧ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p6 p0 p2 p3 p4 p5 p7 : Prop)
theorem file100_61530 : (((((False ∧ True) → False) ∧ ((p7 → False) ∧ (p2 ∧ p6))) ∨ (((p3 ∧ p4) ∧ (p4 ∧ p6)) → ((p6 → p6) ∧ (p5 ∧ p6)))) → ((((False ∧ False) → False) ∨ ((p5 ∧ p4) ∧ (p5 → False))) ∨ (((True → p4) → False) ∧ ((p7 ∧ False) ∧ (p0 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_25
    cases assump_25
    case intro assump_26 assump_27 =>
      apply False.elim assump_26


variable (p4 : Prop)
theorem file100_62399 : (((((p4 → True) → False) → ((False ∨ False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : (((p4 → True) → False) → ((False ∨ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply False.elim assump_7
    case inr assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p4 p5 p0 p7 p1 : Prop)
theorem file100_62867 : ((((((p2 → False) → (p4 → False)) ∧ ((True ∧ p5) → (p4 → p5))) ∧ (((p7 → False) → (False → p2)) → ((True → False) ∨ (p5 → p7)))) ∧ ((((p7 ∧ p5) ∨ (False → False)) ∧ ((p0 ∨ False) → (p1 ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_30 : (((p7 ∧ p5) ∨ (False → False)) ∧ ((p0 ∨ False) → (p1 ∨ p0))) := by
          apply And.intro
          apply Or.inr
          intro assump_17
          apply False.elim assump_17
          intro assump_20
          cases assump_20
          case inl assump_21 =>
            apply Or.inr
            exact assump_21
          case inr assump_22 =>
            apply False.elim assump_22
        let assump_16 := assump_3 assump_30
        apply False.elim assump_16


variable (p1 p4 p3 p7 p2 p6 p0 : Prop)
theorem file100_63821 : (((((p4 ∨ p1) → (True → True)) → False) → (((p7 ∨ p2) → (p3 ∧ False)) → False)) ∨ ((((False → False) ∧ (p7 ∨ p3)) → ((p0 → False) ∧ (p4 ∨ p0))) ∧ (((p3 ∨ p4) → (p6 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_13 : ((p4 ∨ p1) → (True → True)) := by
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_7 := assump_1 assump_13
  apply False.elim assump_7


variable (p4 p0 p6 p3 p5 p7 p1 : Prop)
theorem file100_64300 : (((((p4 → p5) → False) → ((p4 → p5) ∨ (False → False))) ∧ (((p6 ∨ p7) → False) → False)) → ((((True ∧ True) ∧ (p0 ∧ False)) ∧ ((p6 → True) ∧ (p1 → p3))) → False)) := by
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


variable (p2 p5 p3 p6 p4 p7 p0 p1 : Prop)
theorem file100_64836 : (((((False → True) → False) → ((True ∨ p0) ∨ (p4 ∧ p2))) ∧ (((True → p7) → (p7 → False)) → ((p6 → p4) → (p2 ∨ p3)))) → ((((p5 → p1) ∧ (p7 → False)) → False) → (((False ∧ False) ∧ (p1 ∧ p3)) → ((p6 → False) ∨ (False ∨ p6))))) := by
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      apply False.elim assump_16


variable (p1 p2 p4 p5 p3 p6 p0 : Prop)
theorem file100_65329 : (((((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) → False) → ((((p6 → p0) → False) ∧ ((True → False) ∧ (p1 → p1))) ∧ (((True ∨ p2) ∧ (p6 ∧ p3)) → ((p1 ∧ p5) ∧ (p2 ∧ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_474 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      cases assump_8
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inl
          exact assump_10
      case inr assump_15 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          apply Or.inl
          exact assump_22
    case inr assump_11 =>
      cases assump_8
      case inl assump_30 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply Or.inl
          exact assump_11
      case inr assump_31 =>
        cases assump_31
        case intro assump_38 assump_39 =>
          apply Or.inl
          exact assump_38
  let assump_7 := assump_1 assump_474
  apply False.elim assump_7
  apply And.intro
  intro assump_47
  have assump_475 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
    intro assump_53
    intro assump_54
    cases assump_54
    case inl assump_55 =>
      cases assump_53
      case inl assump_59 =>
        cases assump_59
        case intro assump_61 assump_62 =>
          apply Or.inl
          exact assump_55
      case inr assump_60 =>
        cases assump_60
        case intro assump_67 assump_68 =>
          apply Or.inl
          exact assump_67
    case inr assump_56 =>
      cases assump_53
      case inl assump_75 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          apply Or.inl
          exact assump_56
      case inr assump_76 =>
        cases assump_76
        case intro assump_83 assump_84 =>
          apply Or.inl
          exact assump_83
  let assump_52 := assump_1 assump_475
  apply False.elim assump_52
  intro assump_92
  exact assump_92
  intro assump_97
  apply And.intro
  apply And.intro
  cases assump_97
  case intro assump_98 assump_99 =>
    cases assump_98
    case inl assump_100 =>
      cases assump_99
      case intro assump_104 assump_105 =>
        have assump_476 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_113
          intro assump_114
          cases assump_114
          case inl assump_115 =>
            cases assump_113
            case inl assump_119 =>
              cases assump_119
              case intro assump_121 assump_122 =>
                apply Or.inl
                exact assump_115
            case inr assump_120 =>
              cases assump_120
              case intro assump_127 assump_128 =>
                apply Or.inl
                exact assump_127
          case inr assump_116 =>
            cases assump_113
            case inl assump_135 =>
              cases assump_135
              case intro assump_137 assump_138 =>
                apply Or.inl
                exact assump_116
            case inr assump_136 =>
              cases assump_136
              case intro assump_143 assump_144 =>
                apply Or.inl
                exact assump_143
        let assump_112 := assump_1 assump_476
        apply False.elim assump_112
    case inr assump_101 =>
      cases assump_99
      case intro assump_154 assump_155 =>
        have assump_477 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_163
          intro assump_164
          cases assump_164
          case inl assump_165 =>
            cases assump_163
            case inl assump_169 =>
              cases assump_169
              case intro assump_171 assump_172 =>
                apply Or.inl
                exact assump_165
            case inr assump_170 =>
              cases assump_170
              case intro assump_177 assump_178 =>
                apply Or.inl
                exact assump_177
          case inr assump_166 =>
            cases assump_163
            case inl assump_185 =>
              cases assump_185
              case intro assump_187 assump_188 =>
                apply Or.inl
                exact assump_166
            case inr assump_186 =>
              cases assump_186
              case intro assump_193 assump_194 =>
                apply Or.inl
                exact assump_193
        let assump_162 := assump_1 assump_477
        apply False.elim assump_162
  cases assump_97
  case intro assump_202 assump_203 =>
    cases assump_202
    case inl assump_204 =>
      cases assump_203
      case intro assump_208 assump_209 =>
        have assump_478 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_217
          intro assump_218
          cases assump_218
          case inl assump_219 =>
            cases assump_217
            case inl assump_223 =>
              cases assump_223
              case intro assump_225 assump_226 =>
                apply Or.inl
                exact assump_219
            case inr assump_224 =>
              cases assump_224
              case intro assump_231 assump_232 =>
                apply Or.inl
                exact assump_231
          case inr assump_220 =>
            cases assump_217
            case inl assump_239 =>
              cases assump_239
              case intro assump_241 assump_242 =>
                apply Or.inl
                exact assump_220
            case inr assump_240 =>
              cases assump_240
              case intro assump_247 assump_248 =>
                apply Or.inl
                exact assump_247
        let assump_216 := assump_1 assump_478
        apply False.elim assump_216
    case inr assump_205 =>
      cases assump_203
      case intro assump_258 assump_259 =>
        have assump_479 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_267
          intro assump_268
          cases assump_268
          case inl assump_269 =>
            cases assump_267
            case inl assump_273 =>
              cases assump_273
              case intro assump_275 assump_276 =>
                apply Or.inl
                exact assump_269
            case inr assump_274 =>
              cases assump_274
              case intro assump_281 assump_282 =>
                apply Or.inl
                exact assump_281
          case inr assump_270 =>
            cases assump_267
            case inl assump_289 =>
              cases assump_289
              case intro assump_291 assump_292 =>
                apply Or.inl
                exact assump_270
            case inr assump_290 =>
              cases assump_290
              case intro assump_297 assump_298 =>
                apply Or.inl
                exact assump_297
        let assump_266 := assump_1 assump_479
        apply False.elim assump_266
  apply And.intro
  cases assump_97
  case intro assump_306 assump_307 =>
    cases assump_306
    case inl assump_308 =>
      cases assump_307
      case intro assump_312 assump_313 =>
        have assump_480 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_321
          intro assump_322
          cases assump_322
          case inl assump_323 =>
            cases assump_321
            case inl assump_327 =>
              cases assump_327
              case intro assump_329 assump_330 =>
                apply Or.inl
                exact assump_323
            case inr assump_328 =>
              cases assump_328
              case intro assump_335 assump_336 =>
                apply Or.inl
                exact assump_335
          case inr assump_324 =>
            cases assump_321
            case inl assump_343 =>
              cases assump_343
              case intro assump_345 assump_346 =>
                apply Or.inl
                exact assump_324
            case inr assump_344 =>
              cases assump_344
              case intro assump_351 assump_352 =>
                apply Or.inl
                exact assump_351
        let assump_320 := assump_1 assump_480
        apply False.elim assump_320
    case inr assump_309 =>
      cases assump_307
      case intro assump_362 assump_363 =>
        exact assump_309
  cases assump_97
  case intro assump_370 assump_371 =>
    cases assump_370
    case inl assump_372 =>
      cases assump_371
      case intro assump_376 assump_377 =>
        have assump_481 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_385
          intro assump_386
          cases assump_386
          case inl assump_387 =>
            cases assump_385
            case inl assump_391 =>
              cases assump_391
              case intro assump_393 assump_394 =>
                apply Or.inl
                exact assump_387
            case inr assump_392 =>
              cases assump_392
              case intro assump_399 assump_400 =>
                apply Or.inl
                exact assump_399
          case inr assump_388 =>
            cases assump_385
            case inl assump_407 =>
              cases assump_407
              case intro assump_409 assump_410 =>
                apply Or.inl
                exact assump_388
            case inr assump_408 =>
              cases assump_408
              case intro assump_415 assump_416 =>
                apply Or.inl
                exact assump_415
        let assump_384 := assump_1 assump_481
        apply False.elim assump_384
    case inr assump_373 =>
      cases assump_371
      case intro assump_426 assump_427 =>
        have assump_482 : (((p2 ∧ p2) ∨ (p0 ∧ p1)) → ((p0 ∨ p0) → (p0 ∨ p4))) := by
          intro assump_435
          intro assump_436
          cases assump_436
          case inl assump_437 =>
            cases assump_435
            case inl assump_441 =>
              cases assump_441
              case intro assump_443 assump_444 =>
                apply Or.inl
                exact assump_437
            case inr assump_442 =>
              cases assump_442
              case intro assump_449 assump_450 =>
                apply Or.inl
                exact assump_449
          case inr assump_438 =>
            cases assump_435
            case inl assump_457 =>
              cases assump_457
              case intro assump_459 assump_460 =>
                apply Or.inl
                exact assump_438
            case inr assump_458 =>
              cases assump_458
              case intro assump_465 assump_466 =>
                apply Or.inl
                exact assump_465
        let assump_434 := assump_1 assump_482
        apply False.elim assump_434


variable (p5 p7 p3 : Prop)
theorem file100_76166 : ((((((p7 → False) → (False → False)) → False) → False) ∧ ((((False ∨ False) → (p5 ∨ p7)) ∨ ((p3 → True) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False ∨ False) → (p5 ∨ p7)) ∨ ((p3 → True) ∨ (False → False))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p1 p5 p2 p0 : Prop)
theorem file100_76789 : ((((((p5 → False) → False) ∧ ((p4 → True) → False)) → (((False ∨ p1) ∧ (p2 → p0)) → ((p1 ∧ True) ∨ (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p5 → False) → False) ∧ ((p4 → True) → False)) → (((False ∨ p1) ∧ (p2 → p0)) → ((p1 ∧ True) ∨ (True ∧ True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_5
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply And.intro
          exact assump_10
          apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p3 p6 p2 p1 p0 p4 : Prop)
theorem file100_77583 : ((((((False → False) → False) ∨ ((p4 ∨ p3) ∨ (True ∧ p2))) ∧ (((p6 → False) → (False → p1)) → ((p1 → False) ∧ (p1 ∧ True)))) ∧ ((((True → False) ∧ (False ∧ p0)) ∧ ((True ∨ p5) ∨ (True → p2))) ∧ (((p0 ∨ p2) → False) → ((p1 ∧ p3) ∨ (p0 ∨ p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
      case inr assump_7 =>
        cases assump_7
        case inl assump_24 =>
          cases assump_24
          case inl assump_26 =>
            cases assump_3
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                cases assump_34
                case intro assump_36 assump_37 =>
                  cases assump_37
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_40
          case inr assump_27 =>
            cases assump_3
            case intro assump_48 assump_49 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  cases assump_53
                  case intro assump_56 assump_57 =>
                    apply False.elim assump_56
        case inr assump_25 =>
          cases assump_25
          case intro assump_60 assump_61 =>
            cases assump_3
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_70
                case intro assump_72 assump_73 =>
                  cases assump_73
                  case intro assump_76 assump_77 =>
                    apply False.elim assump_76


variable (p6 p0 p5 p2 p4 p1 p7 : Prop)
theorem file100_79774 : (((((p7 ∨ p0) → (p4 → True)) → ((False ∨ True) → (False → False))) ∨ (((p7 ∧ p0) → (True ∧ p0)) ∨ ((p5 → False) ∨ (p1 → False)))) ∨ ((((p2 → False) → (p2 → False)) → ((p0 → p4) → False)) ∨ (((p2 ∧ p5) ∨ (p1 ∧ p5)) ∧ ((p2 → False) ∨ (p6 ∨ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_130
  intro assump_131
  intro assump_132
  apply False.elim assump_132


variable (p0 p7 p4 p2 p1 : Prop)
theorem file100_80200 : ((((((p2 → True) ∨ (p7 → False)) ∨ ((True ∨ p1) ∧ (p0 → p2))) ∨ (((p4 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p2 → True) ∨ (p7 → False)) ∨ ((True ∨ p1) ∧ (p0 → p2))) ∨ (((p4 → False) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p6 p0 p2 p7 p1 p4 : Prop)
theorem file100_80674 : (((((False → False) → False) ∨ ((p6 → p4) → False)) → False) → ((((p4 → False) ∧ (p2 ∨ p1)) → ((p7 ∨ p0) → (p4 → False))) ∨ (((p6 ∧ False) → (p2 → False)) ∨ ((p2 ∧ p2) ∨ (False ∧ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    cases assump_4
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        have assump_55 : p4 := by
          exact assump_6
        let assump_22 := assump_13 assump_55
        apply False.elim assump_22
      case inr assump_18 =>
        have assump_56 : p4 := by
          exact assump_6
        let assump_29 := assump_13 assump_56
        apply False.elim assump_29
  case inr assump_10 =>
    cases assump_4
    case intro assump_35 assump_36 =>
      cases assump_36
      case inl assump_39 =>
        have assump_57 : p4 := by
          exact assump_6
        let assump_44 := assump_35 assump_57
        apply False.elim assump_44
      case inr assump_40 =>
        have assump_58 : p4 := by
          exact assump_6
        let assump_51 := assump_35 assump_58
        apply False.elim assump_51


variable (p4 p7 p3 : Prop)
theorem file100_81894 : (((((p3 ∨ True) ∧ (p4 → p7)) → False) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True → False) → False) := by
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p3 p2 p6 p4 p1 p0 p5 : Prop)
theorem file100_82392 : (((((p0 → p4) → False) → False) → (((p5 ∧ p0) ∨ (p3 ∨ p0)) → ((False → False) ∨ (p4 ∧ p0)))) ∨ ((((p2 ∧ p5) → False) → ((False ∧ p6) ∨ (p2 ∧ True))) ∨ (((p1 ∧ True) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_16 =>
      apply Or.inl
      intro assump_22
      apply False.elim assump_22
    case inr assump_17 =>
      apply Or.inl
      intro assump_29
      apply False.elim assump_29


variable (p7 p5 p3 p1 p4 p2 : Prop)
theorem file100_83103 : ((((((p4 → p4) ∨ (p5 → True)) ∧ ((p3 ∧ p1) → False)) → (((p4 ∨ True) ∨ (p1 → False)) ∧ ((True → p7) ∨ (p2 ∨ p4)))) ∧ ((((True → False) → (False → False)) ∨ ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((True → False) → (False → False)) ∨ ((True → False) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p4 p7 p3 p1 p0 p6 p5 : Prop)
theorem file100_83696 : ((((((False ∧ p6) → (p0 ∨ p3)) ∨ ((p6 ∨ p3) → (p0 → False))) ∨ (((p4 ∧ p4) ∧ (False → False)) ∧ ((p1 ∨ p7) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p6) → (p0 ∨ p3)) ∨ ((p6 ∨ p3) → (p0 → False))) ∨ (((p4 ∧ p4) ∧ (False → False)) ∧ ((p1 ∨ p7) → (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p7 p5 p1 p4 p3 p0 p6 : Prop)
theorem file100_84281 : (((((p1 → p1) → (True → False)) → False) ∨ (((p7 → False) ∨ (True ∧ p1)) ∧ ((p5 → p2) → (p4 → p7)))) ∨ ((((p7 → False) ∨ (p1 → False)) → False) → (((True ∨ p3) ∨ (p5 ∨ p4)) ∧ ((p2 ∨ p6) ∨ (p0 ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_12 : (p1 → p1) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_12
  have assump_13 : True := by
    apply True.intro
  let assump_8 := assump_4 assump_13
  apply False.elim assump_8


variable (p2 p1 p5 p6 p7 p4 p3 : Prop)
theorem file100_84827 : (((((True → False) ∨ (p3 ∧ False)) ∧ ((p2 ∧ p1) → (p3 ∨ p3))) → (((False ∧ False) → False) → False)) ∨ ((((p2 → True) → (p5 → p6)) ∨ ((False ∨ True) ∨ (True ∧ p7))) ∨ (((p4 → False) ∧ (True → False)) ∨ ((p6 → False) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_24 : True := by
        apply True.intro
      let assump_14 := assump_7 assump_24
      apply False.elim assump_14
    case inr assump_8 =>
      cases assump_8
      case intro assump_18 assump_19 =>
        apply False.elim assump_19


variable (p7 p6 p4 p2 p1 p0 p5 : Prop)
theorem file100_85530 : (((((False → False) ∨ (p0 → p1)) → False) → False) ∨ ((((p0 ∨ p4) → False) ∨ ((p7 → p6) → (p1 → p0))) → (((p4 ∧ True) → (p6 ∨ p2)) ∨ ((p5 ∧ p0) → (False → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (p0 → p1)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p7 : Prop)
theorem file100_85968 : ((((((p7 → False) → False) ∧ ((True ∨ p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 → False) → False) ∧ ((True ∨ p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p0 p6 p4 : Prop)
theorem file100_86509 : (((((p0 ∨ p2) ∨ (p6 ∨ True)) → False) → False) ∨ ((((p4 ∧ p6) → (p4 → False)) → False) → (((p0 → p0) ∨ (p2 → False)) ∧ ((p4 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((p0 ∨ p2) ∨ (p6 ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p2 p3 p5 p1 p0 p6 : Prop)
theorem file100_86924 : (((((True ∧ p7) ∨ (p2 → False)) → ((p3 ∧ p5) → (p1 → True))) → False) → ((((p3 → False) ∨ (False ∨ p0)) ∨ ((p6 ∧ p1) ∧ (p5 → p3))) ∧ (((p5 ∨ p5) ∨ (p0 → False)) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_53 : (((True ∧ p7) ∨ (p2 → False)) → ((p3 ∧ p5) → (p1 → True))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    apply True.intro
  let assump_8 := assump_1 assump_53
  apply False.elim assump_8
  intro assump_15
  cases assump_15
  case inl assump_16 =>
    cases assump_16
    case inl assump_18 =>
      have assump_54 : (((True ∧ p7) ∨ (p2 → False)) → ((p3 ∧ p5) → (p1 → True))) := by
        intro assump_25
        intro assump_26
        intro assump_27
        apply True.intro
      let assump_24 := assump_1 assump_54
      apply False.elim assump_24
    case inr assump_19 =>
      have assump_55 : (((True ∧ p7) ∨ (p2 → False)) → ((p3 ∧ p5) → (p1 → True))) := by
        intro assump_36
        intro assump_37
        intro assump_38
        apply True.intro
      let assump_35 := assump_1 assump_55
      apply False.elim assump_35
  case inr assump_17 =>
    have assump_56 : (((True ∧ p7) ∨ (p2 → False)) → ((p3 ∧ p5) → (p1 → True))) := by
      intro assump_47
      intro assump_48
      intro assump_49
      apply True.intro
    let assump_46 := assump_1 assump_56
    apply False.elim assump_46


variable (p4 p2 p5 p6 p7 p1 p0 : Prop)
theorem file100_88398 : (((((p7 ∧ p0) ∨ (p6 ∧ p4)) → ((p7 ∨ p5) ∧ (p7 ∧ True))) → (((p1 → p5) → (p6 ∨ p4)) ∨ ((p7 → p5) → (p2 ∨ p7)))) → ((((p6 → p2) → (False → p4)) ∨ ((p2 ∨ p2) → (False → False))) ∨ (((p7 → False) ∧ (p7 ∧ False)) → ((p0 → p5) → (p5 ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p2 p4 p6 p5 p1 p3 p0 p7 : Prop)
theorem file100_88816 : (((((False ∧ True) ∧ (p4 ∧ p5)) → ((False → False) ∨ (False → p1))) ∨ (((p2 ∧ p0) ∨ (p5 → False)) → False)) → ((((p2 ∧ p7) ∧ (p3 ∧ p0)) ∧ ((p1 → False) ∨ (p1 ∧ True))) → (((False → False) → (p2 ∨ p6)) ∨ ((True ∧ p6) ∧ (False → True))))) := by
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
          cases assump_4
          case inl assump_19 =>
            cases assump_1
            case inl assump_23 =>
              apply Or.inl
              intro assump_27
              apply Or.inl
              exact assump_7
            case inr assump_24 =>
              apply Or.inl
              intro assump_32
              apply Or.inl
              exact assump_7
          case inr assump_20 =>
            cases assump_20
            case intro assump_35 assump_36 =>
              cases assump_1
              case inl assump_41 =>
                apply Or.inl
                intro assump_45
                apply Or.inl
                exact assump_7
              case inr assump_42 =>
                apply Or.inl
                intro assump_50
                apply Or.inl
                exact assump_7


variable (p6 p1 : Prop)
theorem file100_90198 : (((((p1 ∧ p6) ∧ (True → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : (((p1 ∧ p6) ∧ (True → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p0 p7 p2 p1 p4 p3 p5 p6 : Prop)
theorem file100_90750 : (((((p3 → False) → (p6 → p7)) → ((p5 → False) → (p3 ∨ p3))) → (((True ∧ False) → (p2 ∨ p1)) ∨ ((p3 → False) → (p0 ∨ p2)))) ∨ ((((p1 → p4) ∧ (False ∨ p2)) ∨ ((p6 → False) → (p3 → p5))) → (((p7 → p4) → False) ∧ ((p2 → False) ∨ (p7 ∨ p4))))) := by
  apply Or.inl
  intro assump_6
  apply Or.inl
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply False.elim assump_11


variable (p3 p1 p6 p4 p0 p7 : Prop)
theorem file100_91203 : ((((((True → False) ∨ (True ∨ p7)) → ((p3 ∧ p4) → False)) → False) ∧ ((((p0 ∧ False) → (p6 → False)) ∨ ((False ∨ p3) → False)) ∧ (((p7 ∧ p1) ∨ (p4 ∧ p3)) → False))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      cases assump_24
      case inl assump_26 =>
        have assump_118 : (((True → False) ∨ (True ∨ p7)) → ((p3 ∧ p4) → False)) := by
          intro assump_35
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            cases assump_35
            case inl assump_43 =>
              have assump_119 : True := by
                apply True.intro
              let assump_47 := assump_43 assump_119
              apply False.elim assump_47
            case inr assump_44 =>
              cases assump_44
              case inl assump_51 =>
                have assump_120 : ((p7 ∧ p1) ∨ (p4 ∧ p3)) := by
                  apply Or.inr
                  apply And.intro
                  exact assump_38
                  exact assump_37
                let assump_57 := assump_25 assump_120
                apply False.elim assump_57
              case inr assump_52 =>
                have assump_121 : ((p7 ∧ p1) ∨ (p4 ∧ p3)) := by
                  apply Or.inr
                  apply And.intro
                  exact assump_38
                  exact assump_37
                let assump_66 := assump_25 assump_121
                apply False.elim assump_66
        let assump_34 := assump_20 assump_118
        apply False.elim assump_34
      case inr assump_27 =>
        have assump_122 : (((True → False) ∨ (True ∨ p7)) → ((p3 ∧ p4) → False)) := by
          intro assump_80
          intro assump_81
          cases assump_81
          case intro assump_82 assump_83 =>
            cases assump_80
            case inl assump_88 =>
              have assump_123 : True := by
                apply True.intro
              let assump_92 := assump_88 assump_123
              apply False.elim assump_92
            case inr assump_89 =>
              cases assump_89
              case inl assump_96 =>
                have assump_124 : ((p7 ∧ p1) ∨ (p4 ∧ p3)) := by
                  apply Or.inr
                  apply And.intro
                  exact assump_83
                  exact assump_82
                let assump_102 := assump_25 assump_124
                apply False.elim assump_102
              case inr assump_97 =>
                have assump_125 : ((p7 ∧ p1) ∨ (p4 ∧ p3)) := by
                  apply Or.inr
                  apply And.intro
                  exact assump_83
                  exact assump_82
                let assump_111 := assump_25 assump_125
                apply False.elim assump_111
        let assump_79 := assump_20 assump_122
        apply False.elim assump_79


variable (p6 p2 p1 p7 p0 : Prop)
theorem file100_94142 : ((((((p2 ∨ p0) ∨ (p0 → True)) ∧ ((False → False) ∨ (p6 ∨ False))) ∨ (((p1 ∧ p6) ∨ (p2 → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p2 ∨ p0) ∨ (p0 → True)) ∧ ((False → False) ∨ (p6 ∨ False))) ∨ (((p1 ∧ p6) ∨ (p2 → p7)) → False)) := by
    apply Or.inl
    apply And.intro
    apply Or.inr
    intro assump_5
    apply True.intro
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p1 p2 p5 p4 p6 p3 : Prop)
theorem file100_94700 : ((((((p5 → False) → (p5 ∧ True)) → ((p5 ∧ p1) → (p6 → False))) → (((p3 → p6) ∨ (p0 ∨ p6)) ∧ ((p6 ∨ p5) → (False → False)))) ∧ ((((True ∨ p4) ∧ (p1 → False)) → ((False → p2) ∨ (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((True ∨ p4) ∧ (p1 → False)) → ((False → p2) ∨ (p1 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
        case inr assump_13 =>
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
    let assump_8 := assump_3 assump_31
    apply False.elim assump_8


variable (p3 p4 : Prop)
theorem file100_95528 : ((((((p4 ∧ p3) ∨ (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 ∧ p3) ∨ (False → False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p4 ∧ p3) ∨ (False → False)) := by
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p2 p3 p0 p6 : Prop)
theorem file100_96035 : ((((((p3 ∧ False) → (p3 → False)) ∧ ((p2 ∧ p0) ∧ (p6 → True))) → (((p7 ∧ False) ∧ (p6 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 ∧ False) → (p3 → False)) ∧ ((p2 ∧ p0) ∧ (p6 → True))) → (((p7 ∧ False) ∧ (p6 ∨ p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p2 p4 p1 p5 p3 : Prop)
theorem file100_96618 : ((((((p5 ∨ p4) → (p6 ∨ p6)) ∧ ((p2 → True) → (p4 ∧ p1))) → False) ∧ ((((p2 → p1) → False) ∧ ((p6 ∨ p3) ∧ (p5 → False))) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            have assump_50 : ((True → False) → False) := by
              intro assump_23
              have assump_51 : True := by
                apply True.intro
              let assump_26 := assump_23 assump_51
              apply False.elim assump_26
            let assump_22 := assump_7 assump_50
            apply False.elim assump_22
          case inr assump_15 =>
            have assump_52 : ((True → False) → False) := by
              intro assump_40
              have assump_53 : True := by
                apply True.intro
              let assump_43 := assump_40 assump_53
              apply False.elim assump_43
            let assump_39 := assump_7 assump_52
            apply False.elim assump_39


variable (p4 p3 p5 p1 : Prop)
theorem file100_97871 : (((((True ∧ p3) → (p1 ∨ p1)) → ((p4 ∧ p5) → (False ∨ p5))) → False) → False) := by
  intro assump_1
  have assump_18 : (((True ∧ p3) → (p1 ∨ p1)) → ((p4 ∧ p5) → (False ∨ p5))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inr
      exact assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p7 p1 p3 : Prop)
theorem file100_98305 : (((((False ∧ p7) → False) ∧ ((p1 → True) ∨ (p1 → True))) → False) → ((((p4 ∨ p3) → False) ∧ ((p1 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_21 : (((False ∧ p7) → False) ∧ ((p1 → True) ∨ (p1 → True))) := by
      apply And.intro
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
      apply Or.inl
      intro assump_17
      apply True.intro
    let assump_11 := assump_1 assump_21
    apply False.elim assump_11


variable (p3 p2 p4 p0 p1 p7 p6 : Prop)
theorem file100_98943 : (((((p3 → False) ∨ (False ∨ p2)) → False) ∧ (((True → False) ∨ (False → p0)) → ((False → False) ∨ (p4 → False)))) → ((((p6 ∨ p7) ∨ (p6 ∨ p4)) ∨ ((p0 ∧ False) → False)) ∨ (((p2 ∨ p1) → False) → ((True ∨ False) ∧ (True → p3))))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply Or.inl
    apply Or.inr
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_18


variable (p0 p7 p1 p4 p5 p2 p6 p3 : Prop)
theorem file100_99457 : (((((p0 ∧ False) ∨ (p3 ∧ True)) → ((p0 ∧ False) → (p7 ∨ p5))) → False) → ((((True ∧ p4) → (p1 → False)) ∧ ((p1 ∨ p2) → (p6 ∨ p5))) → (((p6 ∧ p4) ∨ (True ∨ p5)) ∨ ((p7 → p0) ∧ (True → p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p2 p5 p0 p3 p6 p1 p4 p7 : Prop)
theorem file100_99877 : ((((((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) → False) ∧ ((((p4 ∨ p5) → False) ∨ ((False ∨ p0) ∧ (True ∨ p4))) ∨ (((p7 ∨ p3) ∨ (False → False)) ∧ ((True ∨ p0) ∧ (p2 ∧ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_249 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
          intro assump_14
          intro assump_15
          cases assump_15
          case inl assump_16 =>
            apply Or.inl
            exact assump_16
          case inr assump_17 =>
            apply False.elim assump_17
        let assump_13 := assump_2 assump_249
        apply False.elim assump_13
      case inr assump_9 =>
        cases assump_9
        case intro assump_27 assump_28 =>
          cases assump_27
          case inl assump_29 =>
            apply False.elim assump_29
          case inr assump_30 =>
            cases assump_28
            case inl assump_35 =>
              have assump_250 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                intro assump_41
                intro assump_42
                cases assump_42
                case inl assump_43 =>
                  apply Or.inl
                  exact assump_43
                case inr assump_44 =>
                  apply False.elim assump_44
              let assump_40 := assump_2 assump_250
              apply False.elim assump_40
            case inr assump_36 =>
              have assump_251 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                intro assump_59
                intro assump_60
                cases assump_60
                case inl assump_61 =>
                  apply Or.inl
                  exact assump_61
                case inr assump_62 =>
                  apply False.elim assump_62
              let assump_58 := assump_2 assump_251
              apply False.elim assump_58
    case inr assump_7 =>
      cases assump_7
      case intro assump_72 assump_73 =>
        cases assump_72
        case inl assump_74 =>
          cases assump_74
          case inl assump_76 =>
            cases assump_73
            case intro assump_80 assump_81 =>
              cases assump_80
              case inl assump_82 =>
                cases assump_81
                case intro assump_86 assump_87 =>
                  have assump_252 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                    intro assump_96
                    intro assump_97
                    cases assump_97
                    case inl assump_98 =>
                      apply Or.inl
                      exact assump_98
                    case inr assump_99 =>
                      apply False.elim assump_99
                  let assump_95 := assump_2 assump_252
                  apply False.elim assump_95
              case inr assump_83 =>
                cases assump_81
                case intro assump_111 assump_112 =>
                  have assump_253 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                    intro assump_122
                    intro assump_123
                    cases assump_123
                    case inl assump_124 =>
                      apply Or.inl
                      exact assump_124
                    case inr assump_125 =>
                      apply False.elim assump_125
                  let assump_121 := assump_2 assump_253
                  apply False.elim assump_121
          case inr assump_77 =>
            cases assump_73
            case intro assump_137 assump_138 =>
              cases assump_137
              case inl assump_139 =>
                cases assump_138
                case intro assump_143 assump_144 =>
                  have assump_254 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                    intro assump_153
                    intro assump_154
                    cases assump_154
                    case inl assump_155 =>
                      apply Or.inl
                      exact assump_155
                    case inr assump_156 =>
                      apply False.elim assump_156
                  let assump_152 := assump_2 assump_254
                  apply False.elim assump_152
              case inr assump_140 =>
                cases assump_138
                case intro assump_168 assump_169 =>
                  have assump_255 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                    intro assump_179
                    intro assump_180
                    cases assump_180
                    case inl assump_181 =>
                      apply Or.inl
                      exact assump_181
                    case inr assump_182 =>
                      apply False.elim assump_182
                  let assump_178 := assump_2 assump_255
                  apply False.elim assump_178
        case inr assump_75 =>
          cases assump_73
          case intro assump_194 assump_195 =>
            cases assump_194
            case inl assump_196 =>
              cases assump_195
              case intro assump_200 assump_201 =>
                have assump_256 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                  intro assump_210
                  intro assump_211
                  cases assump_211
                  case inl assump_212 =>
                    apply Or.inl
                    exact assump_212
                  case inr assump_213 =>
                    apply False.elim assump_213
                let assump_209 := assump_2 assump_256
                apply False.elim assump_209
            case inr assump_197 =>
              cases assump_195
              case intro assump_225 assump_226 =>
                have assump_257 : (((p1 ∨ True) → False) → ((p0 ∨ False) → (p0 ∨ p6))) := by
                  intro assump_236
                  intro assump_237
                  cases assump_237
                  case inl assump_238 =>
                    apply Or.inl
                    exact assump_238
                  case inr assump_239 =>
                    apply False.elim assump_239
                let assump_235 := assump_2 assump_257
                apply False.elim assump_235


variable (p2 p1 p6 p4 p3 p0 p7 : Prop)
theorem file100_106287 : (((((p2 ∨ p6) ∨ (p4 → False)) → ((False → False) → False)) ∧ (((p7 → True) ∨ (p3 ∧ p2)) → False)) → ((((p4 ∨ p6) ∧ (p0 ∧ p1)) ∨ ((p1 → p4) ∨ (True ∨ p1))) → False)) := by
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
          cases assump_1
          case intro assump_17 assump_18 =>
            have assump_90 : ((p7 → True) ∨ (p3 ∧ p2)) := by
              apply Or.inl
              intro assump_24
              apply True.intro
            let assump_23 := assump_18 assump_90
            apply False.elim assump_23
      case inr assump_8 =>
        cases assump_6
        case intro assump_30 assump_31 =>
          cases assump_1
          case intro assump_36 assump_37 =>
            have assump_91 : ((p7 → True) ∨ (p3 ∧ p2)) := by
              apply Or.inl
              intro assump_43
              apply True.intro
            let assump_42 := assump_37 assump_91
            apply False.elim assump_42
  case inr assump_4 =>
    cases assump_4
    case inl assump_47 =>
      cases assump_1
      case intro assump_51 assump_52 =>
        have assump_92 : ((p7 → True) ∨ (p3 ∧ p2)) := by
          apply Or.inl
          intro assump_58
          apply True.intro
        let assump_57 := assump_52 assump_92
        apply False.elim assump_57
    case inr assump_48 =>
      cases assump_48
      case inl assump_62 =>
        cases assump_1
        case intro assump_66 assump_67 =>
          have assump_93 : ((p7 → True) ∨ (p3 ∧ p2)) := by
            apply Or.inl
            intro assump_73
            apply True.intro
          let assump_72 := assump_67 assump_93
          apply False.elim assump_72
      case inr assump_63 =>
        cases assump_1
        case intro assump_79 assump_80 =>
          have assump_94 : ((p7 → True) ∨ (p3 ∧ p2)) := by
            apply Or.inl
            intro assump_86
            apply True.intro
          let assump_85 := assump_80 assump_94
          apply False.elim assump_85


variable (p1 p6 p2 p7 p3 p5 p4 : Prop)
theorem file100_108493 : (((((p6 ∨ p5) → (p3 → False)) ∧ ((p5 ∨ p2) ∧ (True → False))) → (((p4 → True) ∧ (True → p2)) → ((p7 → False) ∧ (p4 → p2)))) ∨ ((((p1 → True) ∧ (p1 ∧ p1)) → ((p3 ∧ True) ∧ (p6 → False))) → (((p7 → False) ∨ (p5 ∧ True)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          have assump_65 : True := by
            apply True.intro
          let assump_24 := assump_17 assump_65
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_66 : True := by
            apply True.intro
          let assump_32 := assump_17 assump_66
          apply False.elim assump_32
  intro assump_36
  cases assump_2
  case intro assump_39 assump_40 =>
    cases assump_1
    case intro assump_45 assump_46 =>
      cases assump_46
      case intro assump_49 assump_50 =>
        cases assump_49
        case inl assump_51 =>
          have assump_67 : True := by
            apply True.intro
          let assump_57 := assump_50 assump_67
          apply False.elim assump_57
        case inr assump_52 =>
          exact assump_52


variable (p0 p2 p5 p7 p1 p6 : Prop)
theorem file100_109879 : (((((True ∨ p0) → False) → ((p6 ∨ p7) → False)) → False) → ((((p7 ∧ p1) → (p5 ∧ p2)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_31 : (((True ∨ p0) → False) → ((p6 ∨ p7) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      have assump_32 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_16 := assump_8 assump_32
      apply False.elim assump_16
    case inr assump_11 =>
      have assump_33 : (True ∨ p0) := by
        apply Or.inl
        apply True.intro
      let assump_24 := assump_8 assump_33
      apply False.elim assump_24
  let assump_7 := assump_1 assump_31
  apply False.elim assump_7


variable (p2 p5 p7 p3 p1 p6 p0 p4 : Prop)
theorem file100_110658 : (((((p2 ∧ p4) → (p4 ∨ p6)) → ((p2 → False) ∨ (p4 → False))) → (((p6 ∧ p7) ∧ (p0 → p6)) ∨ ((p1 ∨ p3) ∨ (True ∧ True)))) ∧ ((((False ∨ p5) ∧ (p0 ∨ p2)) → False) → (((p3 ∨ True) → False) → ((p4 → False) ∨ (p7 → False))))) := by
  apply And.intro
  intro assump_1
  apply Or.inr
  apply Or.inr
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_4
  intro assump_5
  apply Or.inl
  intro assump_10
  have assump_19 : (p3 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_15 := assump_5 assump_19
  apply False.elim assump_15


variable (p0 p7 p6 p2 p3 p4 : Prop)
theorem file100_111273 : ((((((p6 → p4) ∧ (True → False)) → ((p6 ∧ False) → (p3 ∧ p6))) ∨ (((p4 → False) → (p6 → False)) ∨ ((p2 ∨ p0) ∨ (True ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p6 → p4) ∧ (True → False)) → ((p6 ∧ False) → (p3 ∧ p6))) ∨ (((p4 → False) → (p6 → False)) ∨ ((p2 ∨ p0) ∨ (True ∧ p7)))) := by
    apply Or.inl
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


variable (p6 p7 p2 p3 p4 : Prop)
theorem file100_111963 : ((((((p2 → p4) ∨ (p6 ∧ p7)) → ((False ∧ p2) → False)) ∨ (((p7 ∧ p6) ∨ (True ∧ p3)) ∨ ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p4) ∨ (p6 ∧ p7)) → ((False ∧ p2) → False)) ∨ (((p7 ∧ p6) ∨ (True ∧ p3)) ∨ ((p3 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p0 p4 : Prop)
theorem file100_112505 : (((((p0 ∧ p5) → False) → ((p4 → False) → (p4 → p0))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p0 ∧ p5) → False) → ((p4 → False) → (p4 → p0))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_23 : p4 := by
      exact assump_7
    let assump_15 := assump_6 assump_23
    apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p5 p0 p4 p3 : Prop)
theorem file100_112976 : ((((((p0 ∧ p4) → (p3 → False)) ∧ ((p6 → p6) ∧ (False ∨ p5))) → (((False → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p0 ∧ p4) → (p3 → False)) ∧ ((p6 → p6) ∧ (False ∨ p5))) → (((False → False) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          have assump_37 : (False → False) := by
            intro assump_27
            apply False.elim assump_27
          let assump_26 := assump_6 assump_37
          apply False.elim assump_26
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p1 p3 p6 p7 p5 p4 p0 p2 : Prop)
theorem file100_113847 : ((((((p5 → False) ∨ (p6 → p4)) ∨ ((p3 → p0) → (p1 ∨ p6))) → (((False → False) ∧ (p2 → p1)) ∧ ((p5 → False) ∧ (True → False)))) ∧ ((((p3 → False) → (p7 ∨ True)) ∨ ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p3 → False) → (p7 ∨ True)) ∨ ((True → False) → False)) := by
      apply Or.inl
      intro assump_9
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p2 p1 p5 p3 p0 p4 p6 : Prop)
theorem file100_114427 : (((((p5 → False) ∧ (p5 ∨ p5)) → False) ∨ (((p4 → False) ∨ (False → False)) ∨ ((p3 ∨ p1) → False))) ∧ ((((p5 ∨ p0) → (p0 → p0)) → False) → (((p2 → False) ∧ (p6 → p5)) ∧ ((p3 → False) ∨ (p0 ∨ p6))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_81 : p5 := by
        exact assump_6
      let assump_11 := assump_2 assump_81
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_82 : p5 := by
        exact assump_7
      let assump_18 := assump_2 assump_82
      apply False.elim assump_18
  intro assump_22
  apply And.intro
  apply And.intro
  intro assump_23
  have assump_83 : ((p5 ∨ p0) → (p0 → p0)) := by
    intro assump_29
    intro assump_30
    cases assump_29
    case inl assump_33 =>
      exact assump_30
    case inr assump_34 =>
      exact assump_34
  let assump_28 := assump_22 assump_83
  apply False.elim assump_28
  intro assump_42
  have assump_84 : ((p5 ∨ p0) → (p0 → p0)) := by
    intro assump_48
    intro assump_49
    cases assump_48
    case inl assump_52 =>
      exact assump_49
    case inr assump_53 =>
      exact assump_53
  let assump_47 := assump_22 assump_84
  apply False.elim assump_47
  apply Or.inl
  intro assump_63
  have assump_85 : ((p5 ∨ p0) → (p0 → p0)) := by
    intro assump_68
    intro assump_69
    cases assump_68
    case inl assump_72 =>
      exact assump_69
    case inr assump_73 =>
      exact assump_73
  let assump_67 := assump_22 assump_85
  apply False.elim assump_67


variable (p4 p0 p1 p2 p6 p5 : Prop)
theorem file100_116063 : (((((p2 → False) ∨ (p2 ∧ p5)) ∧ ((p4 → p5) → False)) ∧ (((p1 ∨ p0) → False) ∧ ((p2 ∧ p5) ∧ (p6 → p2)))) → ((((p1 → True) ∨ (True ∨ p4)) ∨ ((p5 → p1) → (p6 → False))) ∧ (((p1 → False) → (True ∨ p1)) ∧ ((False → False) ∨ (p2 → True))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply Or.inl
              apply Or.inl
              intro assump_26
              apply True.intro
      case inr assump_7 =>
        cases assump_7
        case intro assump_27 assump_28 =>
          cases assump_3
          case intro assump_35 assump_36 =>
            cases assump_36
            case intro assump_39 assump_40 =>
              cases assump_39
              case intro assump_41 assump_42 =>
                apply Or.inl
                apply Or.inl
                intro assump_49
                apply True.intro
  apply And.intro
  intro assump_50
  cases assump_1
  case intro assump_53 assump_54 =>
    cases assump_53
    case intro assump_55 assump_56 =>
      cases assump_55
      case inl assump_57 =>
        cases assump_54
        case intro assump_63 assump_64 =>
          cases assump_64
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              apply Or.inl
              apply True.intro
      case inr assump_58 =>
        cases assump_58
        case intro assump_77 assump_78 =>
          cases assump_54
          case intro assump_85 assump_86 =>
            cases assump_86
            case intro assump_89 assump_90 =>
              cases assump_89
              case intro assump_91 assump_92 =>
                apply Or.inl
                apply True.intro
  cases assump_1
  case intro assump_99 assump_100 =>
    cases assump_99
    case intro assump_101 assump_102 =>
      cases assump_101
      case inl assump_103 =>
        cases assump_100
        case intro assump_109 assump_110 =>
          cases assump_110
          case intro assump_113 assump_114 =>
            cases assump_113
            case intro assump_115 assump_116 =>
              apply Or.inl
              intro assump_123
              apply False.elim assump_123
      case inr assump_104 =>
        cases assump_104
        case intro assump_126 assump_127 =>
          cases assump_100
          case intro assump_134 assump_135 =>
            cases assump_135
            case intro assump_138 assump_139 =>
              cases assump_138
              case intro assump_140 assump_141 =>
                apply Or.inl
                intro assump_148
                apply False.elim assump_148


variable (p6 p5 p4 p7 p2 p3 : Prop)
theorem file100_119076 : (((((True ∧ True) ∧ (p7 ∨ p3)) ∨ ((True → False) ∨ (p7 → False))) → False) → ((((p5 ∨ p3) ∨ (True ∧ p6)) ∧ ((False → False) ∨ (p2 → False))) → (((True ∧ p4) ∧ (False ∧ p6)) ∨ ((False → p5) ∨ (p5 → False))))) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_12
        case inl assump_19 =>
          apply Or.inr
          apply Or.inl
          intro assump_25
          apply False.elim assump_25
        case inr assump_20 =>
          apply Or.inr
          apply Or.inl
          intro assump_32
          apply False.elim assump_32
      case inr assump_16 =>
        cases assump_12
        case inl assump_37 =>
          apply Or.inr
          apply Or.inl
          intro assump_43
          apply False.elim assump_43
        case inr assump_38 =>
          apply Or.inr
          apply Or.inl
          intro assump_50
          apply False.elim assump_50
    case inr assump_14 =>
      cases assump_14
      case intro assump_53 assump_54 =>
        cases assump_12
        case inl assump_59 =>
          apply Or.inr
          apply Or.inl
          intro assump_65
          apply False.elim assump_65
        case inr assump_60 =>
          apply Or.inr
          apply Or.inl
          intro assump_72
          apply False.elim assump_72


variable (p1 p2 p6 : Prop)
theorem file100_120548 : ((((((p1 ∧ p6) ∧ (True ∨ p1)) → ((True → False) → (p2 ∧ p1))) ∨ (((p1 → False) ∨ (p2 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_55 : ((((p1 ∧ p6) ∧ (True ∨ p1)) → ((True → False) → (p2 ∧ p1))) ∨ (((p1 → False) ∨ (p2 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          have assump_56 : True := by
            apply True.intro
          let assump_23 := assump_6 assump_56
          apply False.elim assump_23
        case inr assump_18 =>
          have assump_57 : True := by
            apply True.intro
          let assump_32 := assump_6 assump_57
          apply False.elim assump_32
    cases assump_5
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_39
        case inl assump_46 =>
          exact assump_40
        case inr assump_47 =>
          exact assump_47
  let assump_4 := assump_1 assump_55
  apply False.elim assump_4


variable (p2 p5 p1 p6 p3 p7 p4 p0 : Prop)
theorem file100_121784 : ((((((p2 → p1) → (p0 → p4)) ∧ ((True ∧ False) ∧ (p3 ∧ p0))) ∧ (((p3 → True) → False) ∧ ((p7 ∧ p2) ∧ (p3 → False)))) ∧ ((((p4 ∨ p5) ∨ (p5 ∧ p6)) ∨ ((p0 ∧ p3) → (p0 → p0))) → False)) → False) := by
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
            apply False.elim assump_13


variable (p5 p7 p3 p2 p4 p0 p6 : Prop)
theorem file100_122399 : ((((((p3 ∧ p3) → False) → ((p5 ∧ p3) → (p4 → False))) ∨ (((p0 → False) ∨ (p3 ∧ p7)) ∨ ((False ∧ p7) → False))) ∧ ((((p2 → p6) → False) ∧ ((False ∧ p4) ∧ (False ∧ False))) ∧ (((True ∧ p7) ∧ (False → False)) ∧ ((p3 → p0) ∨ (p5 ∨ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
    case inr assump_5 =>
      cases assump_5
      case inl assump_20 =>
        cases assump_20
        case inl assump_22 =>
          cases assump_3
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              cases assump_29
              case intro assump_32 assump_33 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  apply False.elim assump_34
        case inr assump_23 =>
          cases assump_23
          case intro assump_38 assump_39 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_52
      case inr assump_21 =>
        cases assump_3
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            cases assump_61
            case intro assump_64 assump_65 =>
              cases assump_64
              case intro assump_66 assump_67 =>
                apply False.elim assump_66


variable (p2 p6 p4 p3 : Prop)
theorem file100_124426 : (((((p4 → p4) → False) → False) ∧ (((p4 ∧ False) → (p4 → p6)) → False)) → ((((p3 → False) → (p4 → False)) → False) → (((p3 ∧ p3) ∨ (p6 ∨ p3)) → ((True → False) ∧ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        have assump_170 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_24
          intro assump_25
          cases assump_24
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
        let assump_23 := assump_18 assump_170
        apply False.elim assump_23
  case inr assump_8 =>
    cases assump_8
    case inl assump_37 =>
      cases assump_1
      case intro assump_43 assump_44 =>
        have assump_171 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_50
          intro assump_51
          cases assump_50
          case intro assump_54 assump_55 =>
            apply False.elim assump_55
        let assump_49 := assump_44 assump_171
        apply False.elim assump_49
    case inr assump_38 =>
      cases assump_1
      case intro assump_67 assump_68 =>
        have assump_172 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_74
          intro assump_75
          cases assump_74
          case intro assump_78 assump_79 =>
            apply False.elim assump_79
        let assump_73 := assump_68 assump_172
        apply False.elim assump_73
  intro assump_87
  cases assump_3
  case inl assump_90 =>
    cases assump_90
    case intro assump_92 assump_93 =>
      cases assump_1
      case intro assump_100 assump_101 =>
        have assump_173 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_107
          intro assump_108
          cases assump_107
          case intro assump_111 assump_112 =>
            apply False.elim assump_112
        let assump_106 := assump_101 assump_173
        apply False.elim assump_106
  case inr assump_91 =>
    cases assump_91
    case inl assump_120 =>
      cases assump_1
      case intro assump_126 assump_127 =>
        have assump_174 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_133
          intro assump_134
          cases assump_133
          case intro assump_137 assump_138 =>
            apply False.elim assump_138
        let assump_132 := assump_127 assump_174
        apply False.elim assump_132
    case inr assump_121 =>
      cases assump_1
      case intro assump_150 assump_151 =>
        have assump_175 : ((p4 ∧ False) → (p4 → p6)) := by
          intro assump_157
          intro assump_158
          cases assump_157
          case intro assump_161 assump_162 =>
            apply False.elim assump_162
        let assump_156 := assump_151 assump_175
        apply False.elim assump_156


variable (p3 p6 p4 p5 p2 p0 p1 : Prop)
theorem file100_127370 : (((((p2 ∨ p2) ∨ (p0 ∨ p6)) ∧ ((False ∧ False) → (p0 ∧ False))) ∨ (((p4 → False) ∧ (p1 → False)) ∧ ((p0 → False) ∨ (p5 ∨ p5)))) → ((((p3 → p1) → False) ∧ ((p1 → False) ∧ (False ∧ p4))) → False)) := by
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p0 p4 p6 p1 p5 p3 p2 p7 : Prop)
theorem file100_127875 : (((((p4 ∧ False) ∨ (p1 → p2)) → ((p2 ∨ True) ∨ (p5 → p4))) ∨ (((p0 ∨ p1) ∨ (p2 ∧ p5)) → ((p6 → False) → False))) ∧ ((((False ∧ p3) → False) ∨ ((p6 ∨ p5) ∨ (p7 ∧ p5))) ∨ (((p6 → p5) ∨ (p1 ∧ p5)) ∨ ((p4 → False) ∧ (p2 ∧ True))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  apply Or.inl
  apply Or.inl
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    apply False.elim assump_13


variable (p7 p3 p6 p2 p1 p4 : Prop)
theorem file100_128557 : (((((p3 → False) ∨ (p3 → True)) ∨ ((p1 → False) → (p2 → False))) → False) → ((((True ∨ p6) ∧ (p4 ∨ p7)) → ((p7 → p6) → False)) → (((p6 → p6) ∨ (p1 → p1)) → ((False → False) ∨ (p1 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  case inr assump_5 =>
    apply Or.inl
    intro assump_21
    apply False.elim assump_21


variable (p1 p5 p6 p0 p2 : Prop)
theorem file100_129059 : ((((((p1 → False) → (False ∨ p6)) → ((p1 → p5) → False)) → (((False → False) ∨ (p2 ∧ p0)) ∨ ((True ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 → False) → (False ∨ p6)) → ((p1 → p5) → False)) → (((False → False) ∨ (p2 ∧ p0)) ∨ ((True ∨ p2) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p7 p0 p4 p3 p6 : Prop)
theorem file100_129582 : ((((((p4 ∨ p0) → False) ∧ ((p4 → False) ∧ (p3 → False))) → (((p6 → p3) → False) → False)) ∧ ((((p1 → False) ∧ (p1 ∨ p7)) → ((p3 ∧ p0) ∨ (False → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((p1 → False) ∧ (p1 ∨ p7)) → ((p3 ∧ p0) ∨ (False → p0))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inr
          intro assump_18
          apply False.elim assump_18
        case inr assump_15 =>
          apply Or.inr
          intro assump_23
          apply False.elim assump_23
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p5 p6 p0 p3 p1 p7 p4 : Prop)
theorem file100_130381 : (((((p5 ∨ p1) → False) ∧ ((p5 → False) → False)) ∧ (((p1 ∨ p0) → (True ∨ p7)) → ((p1 → p7) → (p3 ∨ p6)))) → ((((p4 → False) → False) ∨ ((p1 → p5) → (False ∧ p1))) → (((True → False) → (p3 → p7)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        intro assump_18
        have assump_49 : True := by
          apply True.intro
        let assump_23 := assump_17 assump_49
        apply False.elim assump_23
  case inr assump_4 =>
    cases assump_1
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        apply Or.inl
        intro assump_39
        intro assump_40
        have assump_50 : True := by
          apply True.intro
        let assump_45 := assump_39 assump_50
        apply False.elim assump_45
