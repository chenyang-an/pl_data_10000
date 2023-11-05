variable (p5 p1 p4 p2 p3 : Prop)
theorem file83_41 : ((((((p5 ∨ True) ∨ (p3 ∨ p3)) → False) → (((p2 → False) ∨ (p1 ∨ False)) ∨ ((True ∧ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p5 ∨ True) ∨ (p3 ∨ p3)) → False) → (((p2 → False) ∨ (p1 ∨ False)) ∨ ((True ∧ p4) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_20 : ((p5 ∨ True) ∨ (p3 ∨ p3)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p3 p7 p0 : Prop)
theorem file83_677 : (((((True ∧ False) → (p2 ∨ p3)) → False) → False) ∨ ((((p2 ∧ p2) ∨ (p7 → p2)) → ((p2 → False) → (p3 → False))) ∨ (((p7 → False) → False) → ((p0 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((True ∧ False) → (p2 ∨ p3)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p1 p6 p2 p7 p4 p3 : Prop)
theorem file83_1168 : ((((((p6 → p3) ∧ (p3 → p2)) ∨ ((p4 ∧ p1) → (p7 → False))) → (((p5 ∧ p3) ∧ (p4 ∨ p1)) ∨ ((False → False) → (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 → p3) ∧ (p3 → p2)) ∨ ((p4 ∧ p1) → (p7 → False))) → (((p5 ∧ p3) ∧ (p4 ∨ p1)) ∨ ((False → False) → (p1 → p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        intro assump_14
        intro assump_15
        exact assump_15
    case inr assump_7 =>
      apply Or.inr
      intro assump_22
      intro assump_23
      exact assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 : Prop)
theorem file83_1905 : (((((True ∨ p5) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p5) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p1 p7 p6 p2 p0 p3 : Prop)
theorem file83_2334 : (((((False → p7) → False) → ((True → p3) ∧ (True ∨ p0))) ∨ (((True → False) ∨ (p1 → False)) → False)) ∨ ((((p3 → False) → (p2 → False)) ∨ ((p4 ∨ p6) → False)) ∨ (((False → False) → (p1 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_22
  apply And.intro
  intro assump_23
  have assump_37 : (False → p7) := by
    intro assump_29
    apply False.elim assump_29
  let assump_28 := assump_22 assump_37
  apply False.elim assump_28
  apply Or.inl
  apply True.intro


variable (p2 p4 p3 p7 p6 p5 : Prop)
theorem file83_2881 : ((((((True ∧ p5) → (False ∨ True)) → ((True ∨ p2) → (False → False))) → (((False → False) ∧ (True ∨ p3)) → False)) ∧ ((((p3 → p4) → (False → False)) → False) ∧ (((p2 ∨ p7) ∨ (p5 ∧ p3)) ∧ ((p6 ∨ True) → False)))) → False) := by
  intro assump_55
  cases assump_55
  case intro assump_56 assump_57 =>
    cases assump_57
    case intro assump_60 assump_61 =>
      cases assump_61
      case intro assump_64 assump_65 =>
        cases assump_64
        case inl assump_66 =>
          cases assump_66
          case inl assump_68 =>
            have assump_98 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_74 := assump_65 assump_98
            apply False.elim assump_74
          case inr assump_69 =>
            have assump_99 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_82 := assump_65 assump_99
            apply False.elim assump_82
        case inr assump_67 =>
          cases assump_67
          case intro assump_86 assump_87 =>
            have assump_100 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_94 := assump_65 assump_100
            apply False.elim assump_94


variable (p5 p7 p6 p2 p3 p1 p0 : Prop)
theorem file83_4188 : ((((((False → p2) → False) → ((p6 ∨ p5) ∧ (True → False))) → False) ∨ ((((False → False) ∧ (p7 ∧ p1)) ∨ ((True ∨ True) ∨ (p3 → False))) ∧ (((p3 → p0) ∧ (False ∧ p3)) ∧ ((p1 ∧ p3) ∨ (p3 ∨ p3))))) → False) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    have assump_100 : (((False → p2) → False) → ((p6 ∨ p5) ∧ (True → False))) := by
      intro assump_11
      apply And.intro
      have assump_101 : (False → p2) := by
        intro assump_15
        apply False.elim assump_15
      let assump_14 := assump_11 assump_101
      apply False.elim assump_14
      intro assump_21
      have assump_102 : (False → p2) := by
        intro assump_27
        apply False.elim assump_27
      let assump_26 := assump_11 assump_102
      apply False.elim assump_26
    let assump_10 := assump_6 assump_100
    apply False.elim assump_10
  case inr assump_7 =>
    cases assump_7
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_41
          case intro assump_44 assump_45 =>
            cases assump_37
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                cases assump_53
                case intro assump_56 assump_57 =>
                  apply False.elim assump_56
      case inr assump_39 =>
        cases assump_39
        case inl assump_60 =>
          cases assump_60
          case inl assump_62 =>
            cases assump_37
            case intro assump_66 assump_67 =>
              cases assump_66
              case intro assump_68 assump_69 =>
                cases assump_69
                case intro assump_72 assump_73 =>
                  apply False.elim assump_72
          case inr assump_63 =>
            cases assump_37
            case intro assump_78 assump_79 =>
              cases assump_78
              case intro assump_80 assump_81 =>
                cases assump_81
                case intro assump_84 assump_85 =>
                  apply False.elim assump_84
        case inr assump_61 =>
          cases assump_37
          case intro assump_90 assump_91 =>
            cases assump_90
            case intro assump_92 assump_93 =>
              cases assump_93
              case intro assump_96 assump_97 =>
                apply False.elim assump_96


variable (p2 p7 p4 : Prop)
theorem file83_6656 : ((((((p7 → False) → False) → False) → (((p4 → False) → (p2 → True)) ∨ ((p4 ∧ p4) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p7 → False) → False) → False) → (((p4 → False) → (p2 → True)) ∨ ((p4 ∧ p4) ∨ (True → False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p4 p5 p2 p7 p1 p0 p3 : Prop)
theorem file83_7145 : (((((p4 ∧ p7) ∧ (p0 ∨ p4)) ∨ ((p5 → p2) ∨ (p1 → False))) ∧ (((p2 → False) ∨ (p3 ∨ p7)) ∨ ((p5 ∧ False) → False))) → ((((p5 → False) → False) ∧ ((False → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_14
            case inl assump_21 =>
              cases assump_10
              case inl assump_25 =>
                cases assump_25
                case inl assump_27 =>
                  have assump_249 : (False → False) := by
                    intro assump_36
                    apply False.elim assump_36
                  let assump_35 := assump_4 assump_249
                  apply False.elim assump_35
                case inr assump_28 =>
                  cases assump_28
                  case inl assump_42 =>
                    have assump_250 : (False → False) := by
                      intro assump_51
                      apply False.elim assump_51
                    let assump_50 := assump_4 assump_250
                    apply False.elim assump_50
                  case inr assump_43 =>
                    have assump_251 : (False → False) := by
                      intro assump_64
                      apply False.elim assump_64
                    let assump_63 := assump_4 assump_251
                    apply False.elim assump_63
              case inr assump_26 =>
                have assump_252 : (False → False) := by
                  intro assump_77
                  apply False.elim assump_77
                let assump_76 := assump_4 assump_252
                apply False.elim assump_76
            case inr assump_22 =>
              cases assump_10
              case inl assump_85 =>
                cases assump_85
                case inl assump_87 =>
                  have assump_253 : (False → False) := by
                    intro assump_96
                    apply False.elim assump_96
                  let assump_95 := assump_4 assump_253
                  apply False.elim assump_95
                case inr assump_88 =>
                  cases assump_88
                  case inl assump_102 =>
                    have assump_254 : (False → False) := by
                      intro assump_111
                      apply False.elim assump_111
                    let assump_110 := assump_4 assump_254
                    apply False.elim assump_110
                  case inr assump_103 =>
                    have assump_255 : (False → False) := by
                      intro assump_124
                      apply False.elim assump_124
                    let assump_123 := assump_4 assump_255
                    apply False.elim assump_123
              case inr assump_86 =>
                have assump_256 : (False → False) := by
                  intro assump_137
                  apply False.elim assump_137
                let assump_136 := assump_4 assump_256
                apply False.elim assump_136
      case inr assump_12 =>
        cases assump_12
        case inl assump_143 =>
          cases assump_10
          case inl assump_147 =>
            cases assump_147
            case inl assump_149 =>
              have assump_257 : (False → False) := by
                intro assump_156
                apply False.elim assump_156
              let assump_155 := assump_4 assump_257
              apply False.elim assump_155
            case inr assump_150 =>
              cases assump_150
              case inl assump_162 =>
                have assump_258 : (False → False) := by
                  intro assump_169
                  apply False.elim assump_169
                let assump_168 := assump_4 assump_258
                apply False.elim assump_168
              case inr assump_163 =>
                have assump_259 : (False → False) := by
                  intro assump_180
                  apply False.elim assump_180
                let assump_179 := assump_4 assump_259
                apply False.elim assump_179
          case inr assump_148 =>
            have assump_260 : (False → False) := by
              intro assump_191
              apply False.elim assump_191
            let assump_190 := assump_4 assump_260
            apply False.elim assump_190
        case inr assump_144 =>
          cases assump_10
          case inl assump_199 =>
            cases assump_199
            case inl assump_201 =>
              have assump_261 : (False → False) := by
                intro assump_208
                apply False.elim assump_208
              let assump_207 := assump_4 assump_261
              apply False.elim assump_207
            case inr assump_202 =>
              cases assump_202
              case inl assump_214 =>
                have assump_262 : (False → False) := by
                  intro assump_221
                  apply False.elim assump_221
                let assump_220 := assump_4 assump_262
                apply False.elim assump_220
              case inr assump_215 =>
                have assump_263 : (False → False) := by
                  intro assump_232
                  apply False.elim assump_232
                let assump_231 := assump_4 assump_263
                apply False.elim assump_231
          case inr assump_200 =>
            have assump_264 : (False → False) := by
              intro assump_243
              apply False.elim assump_243
            let assump_242 := assump_4 assump_264
            apply False.elim assump_242


variable (p7 p1 p6 p4 : Prop)
theorem file83_12943 : (((((p6 → False) ∧ (p1 → p7)) → False) ∧ (((p7 ∨ p4) ∨ (p7 → p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p7 ∨ p4) ∨ (p7 → p6)) := by
      apply Or.inr
      intro assump_9
      have assump_21 : ((p7 ∨ p4) ∨ (p7 → p6)) := by
        apply Or.inl
        apply Or.inl
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p3 : Prop)
theorem file83_13500 : (((((False → p3) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p3) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p3) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p1 p5 p0 p7 p2 p4 : Prop)
theorem file83_13943 : (((((False → p0) ∧ (p2 → p0)) ∧ ((p3 → p7) ∨ (p3 ∧ True))) → False) → ((((p5 → p4) → False) ∨ ((p5 → True) → False)) → (((p1 ∨ True) ∨ (p5 → p7)) ∨ ((p4 ∧ p0) → (p5 → p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p4 p0 p6 p5 p7 p1 p3 : Prop)
theorem file83_14428 : (((((p7 → p6) ∨ (p7 → False)) ∨ ((p6 ∨ p7) → False)) → (((False → False) ∨ (p7 → p0)) ∧ ((False → p6) ∨ (False → False)))) ∨ ((((p0 → p0) ∨ (p4 → False)) → False) → (((p4 → p4) ∧ (p3 ∨ True)) ∧ ((p0 ∨ p5) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      apply False.elim assump_8
    case inr assump_5 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
  case inr assump_3 =>
    apply Or.inl
    intro assump_18
    apply False.elim assump_18
  cases assump_1
  case inl assump_21 =>
    cases assump_21
    case inl assump_23 =>
      apply Or.inl
      intro assump_27
      apply False.elim assump_27
    case inr assump_24 =>
      apply Or.inl
      intro assump_32
      apply False.elim assump_32
  case inr assump_22 =>
    apply Or.inl
    intro assump_37
    apply False.elim assump_37


variable (p5 p7 p1 p2 p3 p6 p4 : Prop)
theorem file83_15470 : (((((p5 ∨ p1) ∨ (p1 ∨ p3)) ∨ ((True ∨ p5) ∨ (False ∧ False))) ∨ (((p5 → False) ∨ (p6 → False)) ∨ ((p2 ∨ p1) ∧ (p2 ∧ p4)))) ∨ ((((p7 → False) ∨ (p3 ∧ p3)) → ((p1 ∨ True) ∨ (p6 → True))) ∨ (((False → False) → (p3 ∨ p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p3 p6 p7 p2 p5 p1 : Prop)
theorem file83_15859 : (((((p7 ∧ p2) → (p1 ∨ p2)) → False) ∧ (((p3 → p2) ∨ (p7 ∧ True)) → False)) → ((((p6 → False) → (p2 → p1)) ∧ ((p2 ∧ False) ∧ (p3 ∧ p7))) → (((p6 ∧ False) ∧ (p1 → False)) ∨ ((p7 → p7) → (True → p5))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10


variable (p0 p7 p2 p3 : Prop)
theorem file83_16354 : (((((p0 ∨ p2) ∧ (p0 ∧ False)) → False) → False) → ((((False ∨ p7) ∨ (p3 → p7)) ∨ ((p3 → p2) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        have assump_98 : (((p0 ∨ p2) ∧ (p0 ∧ False)) → False) := by
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_18
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
            case inr assump_20 =>
              cases assump_18
              case intro assump_31 assump_32 =>
                apply False.elim assump_32
        let assump_15 := assump_1 assump_98
        apply False.elim assump_15
    case inr assump_6 =>
      have assump_99 : (((p0 ∨ p2) ∧ (p0 ∧ False)) → False) := by
        intro assump_45
        cases assump_45
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
      let assump_44 := assump_1 assump_99
      apply False.elim assump_44
  case inr assump_4 =>
    have assump_100 : (((p0 ∨ p2) ∧ (p0 ∧ False)) → False) := by
      intro assump_74
      cases assump_74
      case intro assump_75 assump_76 =>
        cases assump_75
        case inl assump_77 =>
          cases assump_76
          case intro assump_81 assump_82 =>
            apply False.elim assump_82
        case inr assump_78 =>
          cases assump_76
          case intro assump_89 assump_90 =>
            apply False.elim assump_90
    let assump_73 := assump_1 assump_100
    apply False.elim assump_73


variable (p1 p5 p2 p4 p6 p0 : Prop)
theorem file83_18462 : (((((p2 ∧ p1) ∧ (False → True)) ∨ ((p2 ∧ False) → (True → p2))) ∨ (((p1 → True) → False) ∨ ((True ∨ p0) ∨ (p4 → False)))) ∨ ((((p6 ∨ False) ∨ (p1 → p0)) ∨ ((p0 ∧ p5) ∨ (p5 ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p0 p5 p1 p3 p4 p7 p6 p2 : Prop)
theorem file83_18884 : (((((p1 ∧ p2) ∧ (p6 ∧ p1)) → False) ∧ (((False → p0) → (p3 → p3)) ∧ ((p0 ∧ p5) ∧ (True → False)))) → ((((p4 ∧ p1) ∨ (True ∧ p1)) ∧ ((p0 ∧ False) ∨ (p2 ∧ p7))) → False)) := by
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case inl assump_20 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_19
        case inl assump_28 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_31
        case inr assump_29 =>
          cases assump_29
          case intro assump_36 assump_37 =>
            cases assump_16
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    have assump_106 : True := by
                      apply True.intro
                    let assump_60 := assump_51 assump_106
                    apply False.elim assump_60
    case inr assump_21 =>
      cases assump_21
      case intro assump_64 assump_65 =>
        cases assump_19
        case inl assump_70 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            apply False.elim assump_73
        case inr assump_71 =>
          cases assump_71
          case intro assump_78 assump_79 =>
            cases assump_16
            case intro assump_84 assump_85 =>
              cases assump_85
              case intro assump_88 assump_89 =>
                cases assump_89
                case intro assump_92 assump_93 =>
                  cases assump_92
                  case intro assump_94 assump_95 =>
                    have assump_107 : True := by
                      apply True.intro
                    let assump_102 := assump_93 assump_107
                    apply False.elim assump_102


variable (p3 p2 p7 p0 p4 : Prop)
theorem file83_20956 : (((((True → False) ∧ (p2 → False)) → ((p7 ∧ False) → False)) ∨ (((p4 ∧ p4) ∧ (False ∧ p0)) → False)) ∨ ((((p7 ∨ False) ∧ (p3 ∨ p0)) → False) ∨ (((p7 ∨ True) ∧ (True → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply False.elim assump_13


variable (p6 p0 p4 p5 p7 p3 p2 : Prop)
theorem file83_21362 : (((((p2 ∨ p2) ∧ (p7 → False)) ∧ ((p4 → True) → (p7 → p5))) ∨ (((p7 ∨ p4) ∨ (p0 → p0)) ∨ ((False ∧ p0) → False))) ∨ ((((True ∨ p5) ∨ (p4 → p5)) ∧ ((p5 → False) ∨ (p7 → p3))) ∨ (((p2 ∧ True) → False) → ((False ∧ False) → (p7 → p6))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_1
  exact assump_1


variable (p5 p7 p3 p6 p0 : Prop)
theorem file83_21752 : (((((False → False) → (p6 → False)) → ((p7 → False) ∧ (p3 ∧ p3))) ∧ (((False → False) → False) ∧ ((p3 ∨ p6) → False))) → ((((True ∨ p6) → False) ∨ ((False → p5) ∨ (False → False))) ∨ (((p0 ∨ p7) → (True → True)) → False))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply Or.inl
      apply Or.inl
      intro assump_16
      cases assump_16
      case inl assump_17 =>
        have assump_36 : (False → False) := by
          intro assump_23
          apply False.elim assump_23
        let assump_22 := assump_10 assump_36
        apply False.elim assump_22
      case inr assump_18 =>
        have assump_37 : (p3 ∨ p6) := by
          apply Or.inr
          exact assump_18
        let assump_32 := assump_11 assump_37
        apply False.elim assump_32


variable (p2 p4 p6 p0 p7 p5 : Prop)
theorem file83_22664 : (((((False → False) → False) ∧ ((p4 ∨ p0) ∧ (p6 → False))) ∧ (((p5 ∨ p2) ∧ (False ∨ p7)) → ((p4 → False) → (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_44 : (False → False) := by
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_4 assump_44
          apply False.elim assump_21
        case inr assump_11 =>
          have assump_45 : (False → False) := by
            intro assump_38
            apply False.elim assump_38
          let assump_37 := assump_4 assump_45
          apply False.elim assump_37


variable (p2 p5 p6 p4 p0 p1 : Prop)
theorem file83_23527 : (((((p2 ∧ p5) ∨ (True → False)) ∧ ((p0 → p4) ∧ (p4 ∧ False))) → (((p6 → False) ∨ (p4 → p1)) ∨ ((p5 ∨ p0) → (True ∨ p0)))) ∨ ((((p0 → p4) ∧ (p4 → p2)) → ((p1 ∧ p6) ∧ (p2 ∧ False))) → False)) := by
  apply Or.inl
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
            apply False.elim assump_17
    case inr assump_5 =>
      cases assump_3
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          apply False.elim assump_29


variable (p3 p2 p7 p0 p4 p5 : Prop)
theorem file83_24332 : ((((((p3 → True) → (p4 → False)) ∨ ((p7 ∨ p4) → (True ∨ p0))) ∧ (((p3 → False) → False) ∧ ((p2 → p0) ∨ (p7 ∨ p7)))) ∧ ((((p5 ∨ True) → False) → ((False → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_136 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
              intro assump_21
              intro assump_22
              have assump_137 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_27 := assump_21 assump_137
              apply False.elim assump_27
            let assump_20 := assump_3 assump_136
            apply False.elim assump_20
          case inr assump_15 =>
            cases assump_15
            case inl assump_34 =>
              have assump_138 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
                intro assump_41
                intro assump_42
                have assump_139 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_47 := assump_41 assump_139
                apply False.elim assump_47
              let assump_40 := assump_3 assump_138
              apply False.elim assump_40
            case inr assump_35 =>
              have assump_140 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
                intro assump_59
                intro assump_60
                have assump_141 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_65 := assump_59 assump_141
                apply False.elim assump_65
              let assump_58 := assump_3 assump_140
              apply False.elim assump_58
      case inr assump_7 =>
        cases assump_5
        case intro assump_74 assump_75 =>
          cases assump_75
          case inl assump_78 =>
            have assump_142 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
              intro assump_85
              intro assump_86
              have assump_143 : (p5 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_91 := assump_85 assump_143
              apply False.elim assump_91
            let assump_84 := assump_3 assump_142
            apply False.elim assump_84
          case inr assump_79 =>
            cases assump_79
            case inl assump_98 =>
              have assump_144 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
                intro assump_105
                intro assump_106
                have assump_145 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_111 := assump_105 assump_145
                apply False.elim assump_111
              let assump_104 := assump_3 assump_144
              apply False.elim assump_104
            case inr assump_99 =>
              have assump_146 : (((p5 ∨ True) → False) → ((False → False) → False)) := by
                intro assump_123
                intro assump_124
                have assump_147 : (p5 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_129 := assump_123 assump_147
                apply False.elim assump_129
              let assump_122 := assump_3 assump_146
              apply False.elim assump_122


variable (p3 p5 : Prop)
theorem file83_28016 : (((((p5 → False) ∧ (p3 ∨ p3)) → ((False ∧ True) ∨ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_37 : (((p5 → False) ∧ (p3 ∨ p3)) → ((False ∧ True) ∨ (p5 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inr
        intro assump_14
        have assump_38 : p5 := by
          exact assump_14
        let assump_19 := assump_6 assump_38
        apply False.elim assump_19
      case inr assump_11 =>
        apply Or.inr
        intro assump_25
        have assump_39 : p5 := by
          exact assump_25
        let assump_30 := assump_6 assump_39
        apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p6 p1 p4 p0 p7 : Prop)
theorem file83_28851 : (((((p4 ∧ p1) ∧ (False → False)) ∧ ((p1 → False) ∧ (p4 ∨ p4))) → False) ∨ ((((p6 ∨ False) → (p0 ∨ p6)) → False) ∨ (((p7 ∨ p7) → (True ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            have assump_38 : p1 := by
              exact assump_11
            let assump_27 := assump_18 assump_38
            apply False.elim assump_27
          case inr assump_23 =>
            have assump_39 : p1 := by
              exact assump_11
            let assump_34 := assump_18 assump_39
            apply False.elim assump_34


variable (p7 p2 p5 p4 : Prop)
theorem file83_29729 : (((((p2 ∧ p7) ∨ (p2 ∨ p5)) ∨ ((False → p4) ∨ (p5 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p2 ∧ p7) ∨ (p2 ∨ p5)) ∨ ((False → p4) ∨ (p5 ∨ p4))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p5 p3 p6 p2 p0 p7 : Prop)
theorem file83_30118 : (((((p4 → p5) ∧ (False → False)) → False) ∨ (((p4 ∨ p0) ∨ (p4 ∨ p6)) → ((True → p7) → (p0 ∨ p0)))) → ((((p6 ∨ p6) ∧ (False ∧ p0)) → ((p3 ∨ p7) ∨ (p3 → p7))) ∧ (((p7 ∨ False) → (False → p5)) ∨ ((p0 ∧ p2) ∧ (p3 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    case inr assump_6 =>
      cases assump_4
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
  cases assump_1
  case inl assump_19 =>
    apply Or.inl
    intro assump_23
    intro assump_24
    apply False.elim assump_24
  case inr assump_20 =>
    apply Or.inl
    intro assump_29
    intro assump_30
    apply False.elim assump_30


variable (p1 p6 p7 p2 p0 p3 p5 : Prop)
theorem file83_31009 : (((((p5 → p0) ∧ (p7 ∧ p5)) ∧ ((p5 ∨ p1) → False)) → (((p1 → False) ∧ (True → False)) ∧ ((p3 → p3) → (p7 → False)))) ∨ ((((p2 → p5) ∨ (p7 ∧ p7)) → ((p5 → p6) ∨ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_68 : (p5 ∨ p1) := by
          apply Or.inl
          exact assump_12
        let assump_19 := assump_6 assump_68
        apply False.elim assump_19
  intro assump_23
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        have assump_69 : (p5 ∨ p1) := by
          apply Or.inl
          exact assump_33
        let assump_40 := assump_27 assump_69
        apply False.elim assump_40
  intro assump_44
  intro assump_45
  cases assump_1
  case intro assump_50 assump_51 =>
    cases assump_50
    case intro assump_52 assump_53 =>
      cases assump_53
      case intro assump_56 assump_57 =>
        have assump_70 : (p5 ∨ p1) := by
          apply Or.inl
          exact assump_57
        let assump_64 := assump_51 assump_70
        apply False.elim assump_64


variable (p0 p1 p7 p2 p4 : Prop)
theorem file83_32417 : ((((((p7 → p7) → False) ∧ ((False → True) → (False ∧ p0))) → (((p2 ∧ p4) ∧ (p1 ∨ p1)) ∧ ((p4 ∧ p4) → (True → False)))) → False) → False) := by
  intro assump_35
  have assump_101 : ((((p7 → p7) → False) ∧ ((False → True) → (False ∧ p0))) → (((p2 ∧ p4) ∧ (p1 ∨ p1)) ∧ ((p4 ∧ p4) → (True → False)))) := by
    intro assump_39
    apply And.intro
    apply And.intro
    apply And.intro
    cases assump_39
    case intro assump_40 assump_41 =>
      have assump_102 : (False → True) := by
        intro assump_47
        apply True.intro
      let assump_46 := assump_41 assump_102
      let assump_48 := And.left assump_46
      apply False.elim assump_48
    cases assump_39
    case intro assump_52 assump_53 =>
      have assump_103 : (False → True) := by
        intro assump_59
        apply True.intro
      let assump_58 := assump_53 assump_103
      let assump_60 := And.left assump_58
      apply False.elim assump_60
    cases assump_39
    case intro assump_64 assump_65 =>
      have assump_104 : (False → True) := by
        intro assump_71
        apply True.intro
      let assump_70 := assump_65 assump_104
      let assump_72 := And.left assump_70
      apply False.elim assump_72
    intro assump_76
    intro assump_77
    cases assump_76
    case intro assump_80 assump_81 =>
      cases assump_39
      case intro assump_86 assump_87 =>
        have assump_105 : (False → True) := by
          intro assump_93
          apply True.intro
        let assump_92 := assump_87 assump_105
        let assump_94 := And.left assump_92
        apply False.elim assump_94
  let assump_38 := assump_35 assump_101
  apply False.elim assump_38


variable (p6 p0 p2 p4 p1 p5 p7 : Prop)
theorem file83_34131 : (((((p1 ∨ p2) → False) → False) ∧ (((p5 → False) → (p7 → False)) → False)) → ((((p6 → False) ∧ (p5 ∨ p6)) → False) ∨ (((p1 → False) → False) ∧ ((p4 ∧ p4) ∨ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        have assump_40 : ((p5 → False) → (p7 → False)) := by
          intro assump_20
          intro assump_21
          have assump_41 : p5 := by
            exact assump_13
          let assump_26 := assump_20 assump_41
          apply False.elim assump_26
        let assump_19 := assump_3 assump_40
        apply False.elim assump_19
      case inr assump_14 =>
        have assump_42 : p6 := by
          exact assump_14
        let assump_36 := assump_9 assump_42
        apply False.elim assump_36


variable (p0 p7 p6 p1 p3 p2 p4 p5 : Prop)
theorem file83_35093 : (((((p7 ∧ p5) ∧ (p1 → False)) → False) ∨ (((p3 ∧ p3) → False) ∧ ((p4 → False) → False))) → ((((p1 → False) ∧ (p0 → False)) ∨ ((p0 ∧ p7) ∨ (p6 → False))) → (((p6 ∧ p1) ∧ (True ∧ p3)) → ((p1 ∨ True) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        cases assump_2
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_1
            case inl assump_26 =>
              apply Or.inl
              apply Or.inl
              exact assump_7
            case inr assump_27 =>
              cases assump_27
              case intro assump_30 assump_31 =>
                apply Or.inl
                apply Or.inl
                exact assump_7
        case inr assump_19 =>
          cases assump_19
          case inl assump_36 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              cases assump_1
              case inl assump_44 =>
                apply Or.inl
                apply Or.inl
                exact assump_7
              case inr assump_45 =>
                cases assump_45
                case intro assump_48 assump_49 =>
                  apply Or.inl
                  apply Or.inl
                  exact assump_7
          case inr assump_37 =>
            cases assump_1
            case inl assump_56 =>
              apply Or.inl
              apply Or.inl
              exact assump_7
            case inr assump_57 =>
              cases assump_57
              case intro assump_60 assump_61 =>
                apply Or.inl
                apply Or.inl
                exact assump_7


variable (p7 p6 p5 p4 p3 : Prop)
theorem file83_36964 : ((((((p4 → p5) → False) ∨ ((p7 → False) ∧ (p5 → False))) → (((p4 → p3) ∨ (p3 → False)) ∧ ((p6 ∨ p3) → False))) ∧ ((((False → False) ∨ (False → False)) ∨ ((p3 ∨ p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → False) ∨ (False → False)) ∨ ((p3 ∨ p4) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p3 p2 p7 p4 p1 p0 : Prop)
theorem file83_37541 : ((((((p2 → False) → False) ∧ ((p0 → p3) ∨ (p1 → p1))) ∧ (((p6 → p2) → (p4 → True)) → False)) ∧ ((((p7 ∧ False) → False) ∧ ((p1 ∨ p4) ∧ (False ∧ p1))) → (((p7 → False) → (p1 ∧ p1)) → ((False ∨ p6) ∧ (p7 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          have assump_52 : ((p6 → p2) → (p4 → True)) := by
            intro assump_27
            intro assump_28
            apply True.intro
          let assump_26 := assump_5 assump_52
          apply False.elim assump_26
        case inr assump_11 =>
          have assump_53 : ((p6 → p2) → (p4 → True)) := by
            intro assump_47
            intro assump_48
            apply True.intro
          let assump_46 := assump_5 assump_53
          apply False.elim assump_46


variable (p0 p6 p1 p5 p4 p2 p3 : Prop)
theorem file83_38553 : (((((p3 ∨ p6) ∧ (p3 → False)) ∧ ((p0 ∨ p0) ∧ (p2 ∨ p2))) ∧ (((False → False) → False) → ((True ∨ p4) ∨ (p3 ∨ p5)))) ∨ ((((p3 ∨ p3) → (p3 ∧ False)) → ((p2 → False) → (False → False))) ∨ (((p5 → p6) ∧ (p2 → p6)) ∨ ((p1 ∨ p5) → (p5 → p2))))) := by
  apply Or.inr
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p7 p2 p0 p3 : Prop)
theorem file83_38961 : (((((p0 ∧ p7) → False) ∧ ((False ∧ p3) ∧ (False → p2))) ∧ (((p3 ∧ p3) ∧ (p2 ∧ p2)) → ((False ∨ p2) ∧ (p3 → p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p3 p6 p0 p5 p4 p1 p2 p7 : Prop)
theorem file83_39440 : (((((p0 → False) ∧ (p2 → False)) → False) ∨ (((p6 ∧ p4) → (p4 → p4)) ∨ ((p5 → p1) ∨ (True ∨ True)))) → ((((True ∨ p1) ∧ (p0 ∧ p1)) ∧ ((p7 → True) ∨ (p4 → False))) ∨ (((False → False) ∨ (p1 ∧ p3)) ∨ ((p1 ∧ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_9 =>
      apply Or.inr
      apply Or.inl
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    case inr assump_10 =>
      cases assump_10
      case inl assump_16 =>
        apply Or.inr
        apply Or.inl
        apply Or.inl
        intro assump_20
        apply False.elim assump_20
      case inr assump_17 =>
        cases assump_17
        case inl assump_23 =>
          apply Or.inr
          apply Or.inl
          apply Or.inl
          intro assump_27
          apply False.elim assump_27
        case inr assump_24 =>
          apply Or.inr
          apply Or.inl
          apply Or.inl
          intro assump_32
          apply False.elim assump_32


variable (p3 p6 : Prop)
theorem file83_40625 : (((((False ∧ False) → False) ∧ ((p3 ∧ False) ∧ (p3 → True))) ∧ (((True ∨ False) → False) → ((p6 → p3) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p6 p2 p5 p0 p3 p7 p1 p4 : Prop)
theorem file83_41103 : (((((p6 ∨ p3) ∨ (p7 → p4)) ∨ ((p7 ∨ p5) → False)) ∨ (((p3 ∨ p4) ∨ (p5 → False)) ∧ ((p3 ∨ False) ∧ (p0 ∨ p7)))) → ((((True ∧ p4) ∧ (True → False)) → False) ∨ (((p1 ∨ p3) → (p7 → False)) ∨ ((p2 → False) ∨ (p5 → False))))) := by
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
          cases assump_12
          case intro assump_13 assump_14 =>
            cases assump_13
            case intro assump_15 assump_16 =>
              have assump_222 : True := by
                apply True.intro
              let assump_23 := assump_14 assump_222
              apply False.elim assump_23
        case inr assump_9 =>
          apply Or.inl
          intro assump_29
          cases assump_29
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              have assump_223 : True := by
                apply True.intro
              let assump_40 := assump_31 assump_223
              apply False.elim assump_40
      case inr assump_7 =>
        apply Or.inl
        intro assump_46
        cases assump_46
        case intro assump_47 assump_48 =>
          cases assump_47
          case intro assump_49 assump_50 =>
            have assump_224 : True := by
              apply True.intro
            let assump_57 := assump_48 assump_224
            apply False.elim assump_57
    case inr assump_5 =>
      apply Or.inl
      intro assump_63
      cases assump_63
      case intro assump_64 assump_65 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          have assump_225 : True := by
            apply True.intro
          let assump_74 := assump_65 assump_225
          apply False.elim assump_74
  case inr assump_3 =>
    cases assump_3
    case intro assump_78 assump_79 =>
      cases assump_78
      case inl assump_80 =>
        cases assump_80
        case inl assump_82 =>
          cases assump_79
          case intro assump_86 assump_87 =>
            cases assump_86
            case inl assump_88 =>
              cases assump_87
              case inl assump_92 =>
                apply Or.inl
                intro assump_96
                cases assump_96
                case intro assump_97 assump_98 =>
                  cases assump_97
                  case intro assump_99 assump_100 =>
                    have assump_226 : True := by
                      apply True.intro
                    let assump_107 := assump_98 assump_226
                    apply False.elim assump_107
              case inr assump_93 =>
                apply Or.inl
                intro assump_113
                cases assump_113
                case intro assump_114 assump_115 =>
                  cases assump_114
                  case intro assump_116 assump_117 =>
                    have assump_227 : True := by
                      apply True.intro
                    let assump_124 := assump_115 assump_227
                    apply False.elim assump_124
            case inr assump_89 =>
              apply False.elim assump_89
        case inr assump_83 =>
          cases assump_79
          case intro assump_132 assump_133 =>
            cases assump_132
            case inl assump_134 =>
              cases assump_133
              case inl assump_138 =>
                apply Or.inl
                intro assump_142
                cases assump_142
                case intro assump_143 assump_144 =>
                  cases assump_143
                  case intro assump_145 assump_146 =>
                    have assump_228 : True := by
                      apply True.intro
                    let assump_153 := assump_144 assump_228
                    apply False.elim assump_153
              case inr assump_139 =>
                apply Or.inl
                intro assump_159
                cases assump_159
                case intro assump_160 assump_161 =>
                  cases assump_160
                  case intro assump_162 assump_163 =>
                    have assump_229 : True := by
                      apply True.intro
                    let assump_170 := assump_161 assump_229
                    apply False.elim assump_170
            case inr assump_135 =>
              apply False.elim assump_135
      case inr assump_81 =>
        cases assump_79
        case intro assump_178 assump_179 =>
          cases assump_178
          case inl assump_180 =>
            cases assump_179
            case inl assump_184 =>
              apply Or.inl
              intro assump_188
              cases assump_188
              case intro assump_189 assump_190 =>
                cases assump_189
                case intro assump_191 assump_192 =>
                  have assump_230 : True := by
                    apply True.intro
                  let assump_199 := assump_190 assump_230
                  apply False.elim assump_199
            case inr assump_185 =>
              apply Or.inl
              intro assump_205
              cases assump_205
              case intro assump_206 assump_207 =>
                cases assump_206
                case intro assump_208 assump_209 =>
                  have assump_231 : True := by
                    apply True.intro
                  let assump_216 := assump_207 assump_231
                  apply False.elim assump_216
          case inr assump_181 =>
            apply False.elim assump_181


variable (p1 p4 p3 p0 p7 : Prop)
theorem file83_46770 : (((((p7 ∧ p1) ∨ (p3 ∨ True)) ∨ ((p4 → False) ∨ (p7 ∧ p4))) → (((p0 ∨ p1) → (p1 → p1)) → False)) → False) := by
  intro assump_1
  have assump_19 : (((p7 ∧ p1) ∨ (p3 ∨ True)) ∨ ((p4 → False) ∨ (p7 ∧ p4))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_19
  have assump_20 : ((p0 ∨ p1) → (p1 → p1)) := by
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      exact assump_7
    case inr assump_11 =>
      exact assump_11
  let assump_5 := assump_4 assump_20
  apply False.elim assump_5


variable (p1 p5 p3 p7 p0 p6 p4 : Prop)
theorem file83_47418 : (((((p0 → False) → False) ∨ ((p3 → False) → False)) → False) → ((((p5 ∨ p5) ∨ (p6 ∧ p5)) → ((p7 ∨ p5) ∧ (True ∨ p4))) ∨ (((p4 → p7) → (p1 ∧ p3)) ∧ ((p0 ∨ True) → (p0 → p5))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inr
      exact assump_7
    case inr assump_8 =>
      apply Or.inr
      exact assump_8
  case inr assump_6 =>
    cases assump_6
    case intro assump_13 assump_14 =>
      apply Or.inr
      exact assump_14
  cases assump_4
  case inl assump_19 =>
    cases assump_19
    case inl assump_21 =>
      apply Or.inl
      apply True.intro
    case inr assump_22 =>
      apply Or.inl
      apply True.intro
  case inr assump_20 =>
    cases assump_20
    case intro assump_27 assump_28 =>
      apply Or.inl
      apply True.intro


variable (p5 p4 p7 p6 p2 p0 : Prop)
theorem file83_48358 : (((((p0 ∧ p5) → (p4 → p6)) → False) ∧ (((False ∨ p2) → (p7 ∨ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((False ∨ p2) → (p7 ∨ p2)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply False.elim assump_10
      case inr assump_11 =>
        apply Or.inr
        exact assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p6 p2 p4 p5 p3 p7 : Prop)
theorem file83_48881 : ((((((False ∧ p7) ∧ (p6 ∧ p6)) ∧ ((p5 ∨ p6) → False)) ∧ (((p3 ∨ p2) → (p1 ∧ p4)) → False)) ∧ ((((p6 ∨ p7) ∧ (p3 ∨ False)) ∧ ((p6 ∧ p2) ∧ (p5 → False))) → False)) → False) := by
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
          case intro assump_10 assump_11 =>
            apply False.elim assump_10


variable (p5 p6 p4 p2 p1 : Prop)
theorem file83_49468 : (((((p1 ∨ p4) ∧ (p5 → p6)) ∨ ((p6 → False) → (False → False))) → False) → ((((p5 ∧ p2) → (p5 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_15 : (((p1 ∨ p4) ∧ (p5 → p6)) ∨ ((p6 → False) → (False → False))) := by
    apply Or.inr
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_7 := assump_1 assump_15
  apply False.elim assump_7


variable (p4 p2 p1 p5 p3 p7 p0 p6 : Prop)
theorem file83_49932 : (((((True ∨ False) ∨ (True ∧ p7)) ∨ ((p3 ∨ p6) → (p1 ∧ p4))) ∨ (((p5 ∨ p3) → (p7 ∨ True)) → False)) → ((((False → False) ∨ (p0 ∧ p1)) ∨ ((p5 ∨ p3) → False)) ∨ (((p7 ∨ p7) ∧ (p2 ∨ p7)) ∧ ((p6 ∨ p4) ∧ (p5 ∧ p1))))) := by
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
          apply Or.inl
          apply Or.inl
          intro assump_12
          apply False.elim assump_12
        case inr assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        cases assump_7
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      intro assump_28
      apply False.elim assump_28
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_33
    apply False.elim assump_33


variable (p7 p1 p0 p3 p2 p5 p6 : Prop)
theorem file83_51098 : ((((((p2 → False) → (p0 ∨ True)) ∧ ((p3 → p6) → (False → p6))) ∨ (((p5 ∨ p7) ∨ (p0 ∧ True)) ∧ ((p7 ∧ p1) ∧ (False ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 → False) → (p0 ∨ True)) ∧ ((p3 → p6) → (False → p6))) ∨ (((p5 ∨ p7) ∨ (p0 ∧ True)) ∧ ((p7 ∧ p1) ∧ (False ∧ p5)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply Or.inr
    apply True.intro
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p2 p1 p6 p5 p0 : Prop)
theorem file83_51695 : (((((False → p5) → False) ∧ ((p0 → False) ∨ (p0 ∧ p4))) ∨ (((p6 → p1) ∧ (p6 ∧ p6)) → ((True ∨ p6) → (p5 ∨ True)))) → ((((p2 ∧ False) ∨ (p6 → False)) → ((p2 ∨ p4) → (False ∨ True))) ∧ (((p4 ∧ False) → False) ∨ ((p0 → False) ∨ (p0 → p5))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    case inr assump_9 =>
      cases assump_1
      case inl assump_18 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_21
          case inl assump_24 =>
            apply Or.inr
            apply True.intro
          case inr assump_25 =>
            cases assump_25
            case intro assump_28 assump_29 =>
              apply Or.inr
              apply True.intro
      case inr assump_19 =>
        apply Or.inr
        apply True.intro
  case inr assump_5 =>
    cases assump_2
    case inl assump_38 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        apply False.elim assump_41
    case inr assump_39 =>
      cases assump_1
      case inl assump_48 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_51
          case inl assump_54 =>
            apply Or.inr
            apply True.intro
          case inr assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              apply Or.inr
              apply True.intro
      case inr assump_49 =>
        apply Or.inr
        apply True.intro
  cases assump_1
  case inl assump_66 =>
    cases assump_66
    case intro assump_68 assump_69 =>
      cases assump_69
      case inl assump_72 =>
        apply Or.inl
        intro assump_76
        cases assump_76
        case intro assump_77 assump_78 =>
          apply False.elim assump_78
      case inr assump_73 =>
        cases assump_73
        case intro assump_83 assump_84 =>
          apply Or.inl
          intro assump_89
          cases assump_89
          case intro assump_90 assump_91 =>
            apply False.elim assump_91
  case inr assump_67 =>
    apply Or.inl
    intro assump_98
    cases assump_98
    case intro assump_99 assump_100 =>
      apply False.elim assump_100


variable (p6 p0 p5 p1 p3 p7 p4 p2 : Prop)
theorem file83_54104 : ((((((p7 ∨ True) → (True ∧ p5)) ∨ ((False ∧ p3) ∨ (p2 → p6))) ∧ (((False → True) → False) → ((p6 → p4) ∨ (p4 → p2)))) ∧ ((((p7 ∨ p7) ∧ (p6 ∧ p6)) ∧ ((True → False) ∧ (p0 → False))) ∧ (((False ∨ p0) ∧ (True ∨ p5)) ∨ ((p1 → p1) ∨ (p5 → False))))) → False) := by
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
              cases assump_16
              case inl assump_18 =>
                cases assump_17
                case intro assump_22 assump_23 =>
                  cases assump_15
                  case intro assump_28 assump_29 =>
                    cases assump_13
                    case inl assump_34 =>
                      cases assump_34
                      case intro assump_36 assump_37 =>
                        cases assump_36
                        case inl assump_38 =>
                          apply False.elim assump_38
                        case inr assump_39 =>
                          cases assump_37
                          case inl assump_44 =>
                            have assump_274 : p0 := by
                              exact assump_39
                            let assump_49 := assump_29 assump_274
                            apply False.elim assump_49
                          case inr assump_45 =>
                            have assump_275 : p0 := by
                              exact assump_39
                            let assump_57 := assump_29 assump_275
                            apply False.elim assump_57
                    case inr assump_35 =>
                      cases assump_35
                      case inl assump_61 =>
                        have assump_276 : True := by
                          apply True.intro
                        let assump_67 := assump_28 assump_276
                        apply False.elim assump_67
                      case inr assump_62 =>
                        have assump_277 : True := by
                          apply True.intro
                        let assump_75 := assump_28 assump_277
                        apply False.elim assump_75
              case inr assump_19 =>
                cases assump_17
                case intro assump_81 assump_82 =>
                  cases assump_15
                  case intro assump_87 assump_88 =>
                    cases assump_13
                    case inl assump_93 =>
                      cases assump_93
                      case intro assump_95 assump_96 =>
                        cases assump_95
                        case inl assump_97 =>
                          apply False.elim assump_97
                        case inr assump_98 =>
                          cases assump_96
                          case inl assump_103 =>
                            have assump_278 : p0 := by
                              exact assump_98
                            let assump_108 := assump_88 assump_278
                            apply False.elim assump_108
                          case inr assump_104 =>
                            have assump_279 : p0 := by
                              exact assump_98
                            let assump_116 := assump_88 assump_279
                            apply False.elim assump_116
                    case inr assump_94 =>
                      cases assump_94
                      case inl assump_120 =>
                        have assump_280 : True := by
                          apply True.intro
                        let assump_126 := assump_87 assump_280
                        apply False.elim assump_126
                      case inr assump_121 =>
                        have assump_281 : True := by
                          apply True.intro
                        let assump_134 := assump_87 assump_281
                        apply False.elim assump_134
      case inr assump_7 =>
        cases assump_7
        case inl assump_138 =>
          cases assump_138
          case intro assump_140 assump_141 =>
            apply False.elim assump_140
        case inr assump_139 =>
          cases assump_3
          case intro assump_148 assump_149 =>
            cases assump_148
            case intro assump_150 assump_151 =>
              cases assump_150
              case intro assump_152 assump_153 =>
                cases assump_152
                case inl assump_154 =>
                  cases assump_153
                  case intro assump_158 assump_159 =>
                    cases assump_151
                    case intro assump_164 assump_165 =>
                      cases assump_149
                      case inl assump_170 =>
                        cases assump_170
                        case intro assump_172 assump_173 =>
                          cases assump_172
                          case inl assump_174 =>
                            apply False.elim assump_174
                          case inr assump_175 =>
                            cases assump_173
                            case inl assump_180 =>
                              have assump_282 : p0 := by
                                exact assump_175
                              let assump_185 := assump_165 assump_282
                              apply False.elim assump_185
                            case inr assump_181 =>
                              have assump_283 : p0 := by
                                exact assump_175
                              let assump_193 := assump_165 assump_283
                              apply False.elim assump_193
                      case inr assump_171 =>
                        cases assump_171
                        case inl assump_197 =>
                          have assump_284 : True := by
                            apply True.intro
                          let assump_203 := assump_164 assump_284
                          apply False.elim assump_203
                        case inr assump_198 =>
                          have assump_285 : True := by
                            apply True.intro
                          let assump_211 := assump_164 assump_285
                          apply False.elim assump_211
                case inr assump_155 =>
                  cases assump_153
                  case intro assump_217 assump_218 =>
                    cases assump_151
                    case intro assump_223 assump_224 =>
                      cases assump_149
                      case inl assump_229 =>
                        cases assump_229
                        case intro assump_231 assump_232 =>
                          cases assump_231
                          case inl assump_233 =>
                            apply False.elim assump_233
                          case inr assump_234 =>
                            cases assump_232
                            case inl assump_239 =>
                              have assump_286 : p0 := by
                                exact assump_234
                              let assump_244 := assump_224 assump_286
                              apply False.elim assump_244
                            case inr assump_240 =>
                              have assump_287 : p0 := by
                                exact assump_234
                              let assump_252 := assump_224 assump_287
                              apply False.elim assump_252
                      case inr assump_230 =>
                        cases assump_230
                        case inl assump_256 =>
                          have assump_288 : True := by
                            apply True.intro
                          let assump_262 := assump_223 assump_288
                          apply False.elim assump_262
                        case inr assump_257 =>
                          have assump_289 : True := by
                            apply True.intro
                          let assump_270 := assump_223 assump_289
                          apply False.elim assump_270


variable (p7 p1 p4 p6 p3 : Prop)
theorem file83_62464 : ((((((True ∨ p6) ∧ (p4 ∧ True)) → False) → (((p4 → True) → False) → False)) ∧ ((((p3 ∨ p6) ∨ (p7 ∧ True)) → ((p1 ∧ True) → (False → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p3 ∨ p6) ∨ (p7 ∧ True)) → ((p1 ∧ True) → (False → p1))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p1 p7 p6 p0 p5 p3 p2 : Prop)
theorem file83_63011 : (((((p2 ∧ p0) ∨ (True ∨ p5)) ∧ ((False → p2) → False)) → False) ∧ ((((p3 → True) ∨ (p1 → p6)) ∨ ((p6 → False) ∧ (p6 → False))) ∨ (((False → p7) ∨ (True ∧ p2)) ∧ ((False → False) ∨ (p7 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_46 : (False → p2) := by
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_3 assump_46
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_21 =>
        have assump_47 : (False → p2) := by
          intro assump_28
          apply False.elim assump_28
        let assump_27 := assump_3 assump_47
        apply False.elim assump_27
      case inr assump_22 =>
        have assump_48 : (False → p2) := by
          intro assump_39
          apply False.elim assump_39
        let assump_38 := assump_3 assump_48
        apply False.elim assump_38
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_45
  apply True.intro


variable (p0 p2 p6 p5 p1 : Prop)
theorem file83_64202 : ((((((False → p2) ∨ (p1 → False)) → False) → (((p5 ∧ p6) ∧ (p1 → False)) → ((p0 → False) → (p0 → False)))) → False) → False) := by
  intro assump_32
  have assump_66 : ((((False → p2) ∨ (p1 → False)) → False) → (((p5 ∧ p6) ∧ (p1 → False)) → ((p0 → False) → (p0 → False)))) := by
    intro assump_36
    intro assump_37
    intro assump_38
    intro assump_39
    cases assump_37
    case intro assump_44 assump_45 =>
      cases assump_44
      case intro assump_46 assump_47 =>
        have assump_67 : ((False → p2) ∨ (p1 → False)) := by
          apply Or.inl
          intro assump_57
          apply False.elim assump_57
        let assump_56 := assump_36 assump_67
        apply False.elim assump_56
  let assump_35 := assump_32 assump_66
  apply False.elim assump_35


variable (p1 p0 p6 p4 p7 p5 : Prop)
theorem file83_65036 : ((((((p0 ∨ p1) ∧ (True → False)) → ((p1 ∧ p7) ∨ (p5 ∨ False))) ∨ (((p5 ∧ p1) ∧ (p1 ∨ p1)) → ((p4 ∧ p0) ∨ (p6 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 ∨ p1) ∧ (True → False)) → ((p1 ∧ p7) ∨ (p5 ∨ False))) ∨ (((p5 ∧ p1) ∧ (p1 ∨ p1)) → ((p4 ∧ p0) ∨ (p6 ∧ p1)))) := by
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


variable (p7 p0 p5 p4 p6 : Prop)
theorem file83_65908 : (((((p4 → p0) → (p6 → p6)) → False) ∧ (((p6 ∧ p0) ∧ (p5 ∨ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p4 → p0) → (p6 → p6)) := by
      intro assump_10
      intro assump_11
      exact assump_11
    let assump_9 := assump_2 assump_19
    apply False.elim assump_9


variable (p2 p3 : Prop)
theorem file83_66298 : ((((((True → False) ∧ (p2 ∧ p3)) ∧ ((p2 ∧ False) ∧ (p2 → False))) → False) → False) → False) := by
  intro assump_9
  have assump_37 : ((((True → False) ∧ (p2 ∧ p3)) ∧ ((p2 ∧ False) ∧ (p2 → False))) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply False.elim assump_29
  let assump_12 := assump_9 assump_37
  apply False.elim assump_12


variable (p0 p6 p1 : Prop)
theorem file83_67021 : ((((((p0 → False) → (p6 → False)) → False) → False) ∧ ((((p0 ∧ False) ∧ (p1 ∨ p0)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p0 ∧ False) ∧ (p1 ∨ p0)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p3 p1 p0 p7 p2 p5 p4 p6 : Prop)
theorem file83_67590 : ((((((False → False) ∧ (p7 → False)) ∨ ((p3 ∨ p7) ∧ (p0 ∨ p0))) ∨ (((p7 ∧ p7) ∧ (p2 → p7)) → ((p1 → p2) ∨ (p2 → p7)))) ∧ ((((p6 → False) ∨ (p3 → p3)) ∨ ((p6 → False) ∨ (p2 → p4))) ∧ (((p5 ∧ p7) ∨ (p3 → p3)) → False))) → False) := by
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
            cases assump_14
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                have assump_348 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                  apply Or.inr
                  intro assump_25
                  exact assump_25
                let assump_24 := assump_15 assump_348
                apply False.elim assump_24
              case inr assump_19 =>
                have assump_349 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                  apply Or.inr
                  intro assump_36
                  exact assump_36
                let assump_35 := assump_15 assump_349
                apply False.elim assump_35
            case inr assump_17 =>
              cases assump_17
              case inl assump_42 =>
                have assump_350 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                  apply Or.inr
                  intro assump_49
                  exact assump_49
                let assump_48 := assump_15 assump_350
                apply False.elim assump_48
              case inr assump_43 =>
                have assump_351 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                  apply Or.inr
                  intro assump_60
                  exact assump_60
                let assump_59 := assump_15 assump_351
                apply False.elim assump_59
      case inr assump_7 =>
        cases assump_7
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            cases assump_67
            case inl assump_72 =>
              cases assump_3
              case intro assump_76 assump_77 =>
                cases assump_76
                case inl assump_78 =>
                  cases assump_78
                  case inl assump_80 =>
                    have assump_352 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_87
                      exact assump_87
                    let assump_86 := assump_77 assump_352
                    apply False.elim assump_86
                  case inr assump_81 =>
                    have assump_353 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_98
                      exact assump_98
                    let assump_97 := assump_77 assump_353
                    apply False.elim assump_97
                case inr assump_79 =>
                  cases assump_79
                  case inl assump_104 =>
                    have assump_354 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_111
                      exact assump_111
                    let assump_110 := assump_77 assump_354
                    apply False.elim assump_110
                  case inr assump_105 =>
                    have assump_355 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_122
                      exact assump_122
                    let assump_121 := assump_77 assump_355
                    apply False.elim assump_121
            case inr assump_73 =>
              cases assump_3
              case intro assump_130 assump_131 =>
                cases assump_130
                case inl assump_132 =>
                  cases assump_132
                  case inl assump_134 =>
                    have assump_356 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_141
                      exact assump_141
                    let assump_140 := assump_131 assump_356
                    apply False.elim assump_140
                  case inr assump_135 =>
                    have assump_357 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_152
                      exact assump_152
                    let assump_151 := assump_131 assump_357
                    apply False.elim assump_151
                case inr assump_133 =>
                  cases assump_133
                  case inl assump_158 =>
                    have assump_358 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_165
                      exact assump_165
                    let assump_164 := assump_131 assump_358
                    apply False.elim assump_164
                  case inr assump_159 =>
                    have assump_359 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_176
                      exact assump_176
                    let assump_175 := assump_131 assump_359
                    apply False.elim assump_175
          case inr assump_69 =>
            cases assump_67
            case inl assump_184 =>
              cases assump_3
              case intro assump_188 assump_189 =>
                cases assump_188
                case inl assump_190 =>
                  cases assump_190
                  case inl assump_192 =>
                    have assump_360 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_199
                      exact assump_199
                    let assump_198 := assump_189 assump_360
                    apply False.elim assump_198
                  case inr assump_193 =>
                    have assump_361 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_210
                      exact assump_210
                    let assump_209 := assump_189 assump_361
                    apply False.elim assump_209
                case inr assump_191 =>
                  cases assump_191
                  case inl assump_216 =>
                    have assump_362 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_223
                      exact assump_223
                    let assump_222 := assump_189 assump_362
                    apply False.elim assump_222
                  case inr assump_217 =>
                    have assump_363 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_234
                      exact assump_234
                    let assump_233 := assump_189 assump_363
                    apply False.elim assump_233
            case inr assump_185 =>
              cases assump_3
              case intro assump_242 assump_243 =>
                cases assump_242
                case inl assump_244 =>
                  cases assump_244
                  case inl assump_246 =>
                    have assump_364 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_253
                      exact assump_253
                    let assump_252 := assump_243 assump_364
                    apply False.elim assump_252
                  case inr assump_247 =>
                    have assump_365 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_264
                      exact assump_264
                    let assump_263 := assump_243 assump_365
                    apply False.elim assump_263
                case inr assump_245 =>
                  cases assump_245
                  case inl assump_270 =>
                    have assump_366 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_277
                      exact assump_277
                    let assump_276 := assump_243 assump_366
                    apply False.elim assump_276
                  case inr assump_271 =>
                    have assump_367 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
                      apply Or.inr
                      intro assump_288
                      exact assump_288
                    let assump_287 := assump_243 assump_367
                    apply False.elim assump_287
    case inr assump_5 =>
      cases assump_3
      case intro assump_296 assump_297 =>
        cases assump_296
        case inl assump_298 =>
          cases assump_298
          case inl assump_300 =>
            have assump_368 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
              apply Or.inr
              intro assump_307
              exact assump_307
            let assump_306 := assump_297 assump_368
            apply False.elim assump_306
          case inr assump_301 =>
            have assump_369 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
              apply Or.inr
              intro assump_318
              exact assump_318
            let assump_317 := assump_297 assump_369
            apply False.elim assump_317
        case inr assump_299 =>
          cases assump_299
          case inl assump_324 =>
            have assump_370 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
              apply Or.inr
              intro assump_331
              exact assump_331
            let assump_330 := assump_297 assump_370
            apply False.elim assump_330
          case inr assump_325 =>
            have assump_371 : ((p5 ∧ p7) ∨ (p3 → p3)) := by
              apply Or.inr
              intro assump_342
              exact assump_342
            let assump_341 := assump_297 assump_371
            apply False.elim assump_341


variable (p2 p7 p5 p1 p4 p0 p3 p6 : Prop)
theorem file83_77521 : (((((p7 ∨ p3) ∨ (p1 ∨ p0)) ∧ ((p2 → False) → (True → p3))) ∧ (((False → False) → (p0 ∧ False)) ∧ ((p2 → False) ∧ (p2 ∧ p1)))) → ((((p6 ∨ p2) ∧ (p1 ∨ p7)) → ((p3 → p0) ∨ (p7 ∨ p1))) ∧ (((p2 → False) ∧ (p0 → p2)) → ((p5 → True) ∧ (p4 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              cases assump_17
              case inl assump_19 =>
                cases assump_14
                case intro assump_25 assump_26 =>
                  cases assump_26
                  case intro assump_29 assump_30 =>
                    cases assump_30
                    case intro assump_33 assump_34 =>
                      apply Or.inl
                      intro assump_39
                      have assump_600 : p2 := by
                        exact assump_33
                      let assump_45 := assump_29 assump_600
                      apply False.elim assump_45
              case inr assump_20 =>
                cases assump_14
                case intro assump_53 assump_54 =>
                  cases assump_54
                  case intro assump_57 assump_58 =>
                    cases assump_58
                    case intro assump_61 assump_62 =>
                      apply Or.inl
                      intro assump_67
                      have assump_601 : p2 := by
                        exact assump_61
                      let assump_73 := assump_57 assump_601
                      apply False.elim assump_73
            case inr assump_18 =>
              cases assump_18
              case inl assump_77 =>
                cases assump_14
                case intro assump_83 assump_84 =>
                  cases assump_84
                  case intro assump_87 assump_88 =>
                    cases assump_88
                    case intro assump_91 assump_92 =>
                      apply Or.inl
                      intro assump_97
                      have assump_602 : p2 := by
                        exact assump_91
                      let assump_103 := assump_87 assump_602
                      apply False.elim assump_103
              case inr assump_78 =>
                cases assump_14
                case intro assump_111 assump_112 =>
                  cases assump_112
                  case intro assump_115 assump_116 =>
                    cases assump_116
                    case intro assump_119 assump_120 =>
                      apply Or.inl
                      intro assump_125
                      exact assump_78
      case inr assump_10 =>
        cases assump_1
        case intro assump_130 assump_131 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            cases assump_132
            case inl assump_134 =>
              cases assump_134
              case inl assump_136 =>
                cases assump_131
                case intro assump_142 assump_143 =>
                  cases assump_143
                  case intro assump_146 assump_147 =>
                    cases assump_147
                    case intro assump_150 assump_151 =>
                      apply Or.inl
                      intro assump_156
                      have assump_603 : p2 := by
                        exact assump_150
                      let assump_162 := assump_146 assump_603
                      apply False.elim assump_162
              case inr assump_137 =>
                cases assump_131
                case intro assump_170 assump_171 =>
                  cases assump_171
                  case intro assump_174 assump_175 =>
                    cases assump_175
                    case intro assump_178 assump_179 =>
                      apply Or.inl
                      intro assump_184
                      have assump_604 : p2 := by
                        exact assump_178
                      let assump_190 := assump_174 assump_604
                      apply False.elim assump_190
            case inr assump_135 =>
              cases assump_135
              case inl assump_194 =>
                cases assump_131
                case intro assump_200 assump_201 =>
                  cases assump_201
                  case intro assump_204 assump_205 =>
                    cases assump_205
                    case intro assump_208 assump_209 =>
                      apply Or.inl
                      intro assump_214
                      have assump_605 : p2 := by
                        exact assump_208
                      let assump_220 := assump_204 assump_605
                      apply False.elim assump_220
              case inr assump_195 =>
                cases assump_131
                case intro assump_228 assump_229 =>
                  cases assump_229
                  case intro assump_232 assump_233 =>
                    cases assump_233
                    case intro assump_236 assump_237 =>
                      apply Or.inl
                      intro assump_242
                      exact assump_195
    case inr assump_6 =>
      cases assump_4
      case inl assump_247 =>
        cases assump_1
        case intro assump_251 assump_252 =>
          cases assump_251
          case intro assump_253 assump_254 =>
            cases assump_253
            case inl assump_255 =>
              cases assump_255
              case inl assump_257 =>
                cases assump_252
                case intro assump_263 assump_264 =>
                  cases assump_264
                  case intro assump_267 assump_268 =>
                    cases assump_268
                    case intro assump_271 assump_272 =>
                      apply Or.inl
                      intro assump_277
                      have assump_606 : p2 := by
                        exact assump_271
                      let assump_283 := assump_267 assump_606
                      apply False.elim assump_283
              case inr assump_258 =>
                cases assump_252
                case intro assump_291 assump_292 =>
                  cases assump_292
                  case intro assump_295 assump_296 =>
                    cases assump_296
                    case intro assump_299 assump_300 =>
                      apply Or.inl
                      intro assump_305
                      have assump_607 : p2 := by
                        exact assump_299
                      let assump_311 := assump_295 assump_607
                      apply False.elim assump_311
            case inr assump_256 =>
              cases assump_256
              case inl assump_315 =>
                cases assump_252
                case intro assump_321 assump_322 =>
                  cases assump_322
                  case intro assump_325 assump_326 =>
                    cases assump_326
                    case intro assump_329 assump_330 =>
                      apply Or.inl
                      intro assump_335
                      have assump_608 : p2 := by
                        exact assump_329
                      let assump_341 := assump_325 assump_608
                      apply False.elim assump_341
              case inr assump_316 =>
                cases assump_252
                case intro assump_349 assump_350 =>
                  cases assump_350
                  case intro assump_353 assump_354 =>
                    cases assump_354
                    case intro assump_357 assump_358 =>
                      apply Or.inl
                      intro assump_363
                      exact assump_316
      case inr assump_248 =>
        cases assump_1
        case intro assump_368 assump_369 =>
          cases assump_368
          case intro assump_370 assump_371 =>
            cases assump_370
            case inl assump_372 =>
              cases assump_372
              case inl assump_374 =>
                cases assump_369
                case intro assump_380 assump_381 =>
                  cases assump_381
                  case intro assump_384 assump_385 =>
                    cases assump_385
                    case intro assump_388 assump_389 =>
                      apply Or.inl
                      intro assump_394
                      have assump_609 : p2 := by
                        exact assump_388
                      let assump_400 := assump_384 assump_609
                      apply False.elim assump_400
              case inr assump_375 =>
                cases assump_369
                case intro assump_408 assump_409 =>
                  cases assump_409
                  case intro assump_412 assump_413 =>
                    cases assump_413
                    case intro assump_416 assump_417 =>
                      apply Or.inl
                      intro assump_422
                      have assump_610 : p2 := by
                        exact assump_416
                      let assump_428 := assump_412 assump_610
                      apply False.elim assump_428
            case inr assump_373 =>
              cases assump_373
              case inl assump_432 =>
                cases assump_369
                case intro assump_438 assump_439 =>
                  cases assump_439
                  case intro assump_442 assump_443 =>
                    cases assump_443
                    case intro assump_446 assump_447 =>
                      apply Or.inl
                      intro assump_452
                      have assump_611 : p2 := by
                        exact assump_446
                      let assump_458 := assump_442 assump_611
                      apply False.elim assump_458
              case inr assump_433 =>
                cases assump_369
                case intro assump_466 assump_467 =>
                  cases assump_467
                  case intro assump_470 assump_471 =>
                    cases assump_471
                    case intro assump_474 assump_475 =>
                      apply Or.inl
                      intro assump_480
                      exact assump_433
  intro assump_483
  apply And.intro
  intro assump_484
  apply True.intro
  intro assump_485
  cases assump_483
  case intro assump_488 assump_489 =>
    cases assump_1
    case intro assump_494 assump_495 =>
      cases assump_494
      case intro assump_496 assump_497 =>
        cases assump_496
        case inl assump_498 =>
          cases assump_498
          case inl assump_500 =>
            cases assump_495
            case intro assump_506 assump_507 =>
              cases assump_507
              case intro assump_510 assump_511 =>
                cases assump_511
                case intro assump_514 assump_515 =>
                  have assump_612 : p2 := by
                    exact assump_514
                  let assump_522 := assump_510 assump_612
                  apply False.elim assump_522
          case inr assump_501 =>
            cases assump_495
            case intro assump_530 assump_531 =>
              cases assump_531
              case intro assump_534 assump_535 =>
                cases assump_535
                case intro assump_538 assump_539 =>
                  have assump_613 : p2 := by
                    exact assump_538
                  let assump_546 := assump_534 assump_613
                  apply False.elim assump_546
        case inr assump_499 =>
          cases assump_499
          case inl assump_550 =>
            cases assump_495
            case intro assump_556 assump_557 =>
              cases assump_557
              case intro assump_560 assump_561 =>
                cases assump_561
                case intro assump_564 assump_565 =>
                  have assump_614 : p2 := by
                    exact assump_564
                  let assump_572 := assump_560 assump_614
                  apply False.elim assump_572
          case inr assump_551 =>
            cases assump_495
            case intro assump_580 assump_581 =>
              cases assump_581
              case intro assump_584 assump_585 =>
                cases assump_585
                case intro assump_588 assump_589 =>
                  have assump_615 : p2 := by
                    exact assump_588
                  let assump_596 := assump_584 assump_615
                  apply False.elim assump_596


variable (p2 p7 p0 p4 p1 : Prop)
theorem file83_90196 : ((((((p4 → p2) → (p7 ∧ p4)) ∨ ((False → False) → (p7 → False))) → (((p4 ∨ p0) ∨ (p4 ∧ p1)) → ((False ∧ True) → False))) → False) → False) := by
  intro assump_5
  have assump_19 : ((((p4 → p2) → (p7 ∧ p4)) ∨ ((False → False) → (p7 → False))) → (((p4 ∨ p0) ∨ (p4 ∧ p1)) → ((False ∧ True) → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p1 p0 p4 : Prop)
theorem file83_90766 : (((((False ∧ False) ∧ (p4 → False)) → ((p0 ∧ p1) ∨ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∧ False) ∧ (p4 → False)) → ((p0 ∧ p1) ∨ (p1 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p5 p6 : Prop)
theorem file83_91245 : (((((False → False) → False) ∧ ((p6 ∨ p5) ∧ (p3 → p5))) ∨ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_51 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_4 assump_51
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_52 : (False → False) := by
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_4 assump_52
          apply False.elim assump_31
  case inr assump_3 =>
    have assump_53 : ((True → False) → False) := by
      intro assump_41
      have assump_54 : True := by
        apply True.intro
      let assump_44 := assump_41 assump_54
      apply False.elim assump_44
    let assump_40 := assump_3 assump_53
    apply False.elim assump_40


variable (p6 p4 p0 p5 p7 p2 p1 p3 : Prop)
theorem file83_92375 : ((((((p7 → False) ∨ (p6 ∨ p5)) ∧ ((p4 ∨ p7) ∧ (p7 → p2))) ∨ (((p0 → p4) ∧ (False ∨ False)) → ((p5 ∧ p7) ∨ (p0 → p7)))) ∧ ((((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) → False)) → False) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_31
    case inl assump_33 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_35
        case inl assump_37 =>
          cases assump_36
          case intro assump_41 assump_42 =>
            cases assump_41
            case inl assump_43 =>
              have assump_127 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_51 := assump_32 assump_127
              apply False.elim assump_51
            case inr assump_44 =>
              have assump_128 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply True.intro
              let assump_61 := assump_32 assump_128
              apply False.elim assump_61
        case inr assump_38 =>
          cases assump_38
          case inl assump_65 =>
            cases assump_36
            case intro assump_69 assump_70 =>
              cases assump_69
              case inl assump_71 =>
                have assump_129 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_79 := assump_32 assump_129
                apply False.elim assump_79
              case inr assump_72 =>
                have assump_130 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_89 := assump_32 assump_130
                apply False.elim assump_89
          case inr assump_66 =>
            cases assump_36
            case intro assump_95 assump_96 =>
              cases assump_95
              case inl assump_97 =>
                have assump_131 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_105 := assump_32 assump_131
                apply False.elim assump_105
              case inr assump_98 =>
                have assump_132 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_115 := assump_32 assump_132
                apply False.elim assump_115
    case inr assump_34 =>
      have assump_133 : (((True ∨ p1) ∨ (p4 → False)) ∨ ((p5 ∧ p3) → False)) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_123 := assump_32 assump_133
      apply False.elim assump_123


variable (p7 p1 p0 p5 p2 p6 : Prop)
theorem file83_95667 : (((((p5 ∨ p0) → False) → ((p0 ∧ p7) → (p7 ∧ p5))) ∨ (((p1 → False) ∧ (p5 ∨ p7)) ∧ ((p1 ∨ p1) → False))) ∨ ((((p6 → False) → False) → False) ∨ (((p2 → False) ∨ (p7 → True)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    exact assump_4
  cases assump_2
  case intro assump_11 assump_12 =>
    have assump_23 : (p5 ∨ p0) := by
      apply Or.inr
      exact assump_11
    let assump_19 := assump_1 assump_23
    apply False.elim assump_19


variable (p6 p3 p1 p2 p0 p5 : Prop)
theorem file83_96270 : (((((p0 → p5) ∧ (p2 → False)) → ((p1 ∨ p2) → False)) → False) → ((((p3 ∨ p6) → (p2 → False)) ∨ ((True → False) → False)) ∨ (((p0 ∨ p0) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_82 : (((p0 → p5) ∧ (p2 → False)) → ((p1 ∨ p2) → False)) := by
      intro assump_15
      intro assump_16
      cases assump_16
      case inl assump_17 =>
        cases assump_15
        case intro assump_21 assump_22 =>
          have assump_83 : p2 := by
            exact assump_5
          let assump_27 := assump_22 assump_83
          apply False.elim assump_27
      case inr assump_18 =>
        cases assump_15
        case intro assump_33 assump_34 =>
          have assump_84 : p2 := by
            exact assump_18
          let assump_39 := assump_34 assump_84
          apply False.elim assump_39
    let assump_14 := assump_1 assump_82
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_85 : (((p0 → p5) ∧ (p2 → False)) → ((p1 ∨ p2) → False)) := by
      intro assump_51
      intro assump_52
      cases assump_52
      case inl assump_53 =>
        cases assump_51
        case intro assump_57 assump_58 =>
          have assump_86 : p2 := by
            exact assump_5
          let assump_63 := assump_58 assump_86
          apply False.elim assump_63
      case inr assump_54 =>
        cases assump_51
        case intro assump_69 assump_70 =>
          have assump_87 : p2 := by
            exact assump_54
          let assump_75 := assump_70 assump_87
          apply False.elim assump_75
    let assump_50 := assump_1 assump_85
    apply False.elim assump_50


variable (p5 p4 p7 p1 p2 : Prop)
theorem file83_98028 : (((((False → p1) → False) → False) → False) → ((((p1 ∧ p4) → False) ∧ ((p5 → False) → False)) → (((p5 ∨ p7) ∧ (p5 ∧ False)) ∨ ((p2 ∨ p5) → (p5 → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    intro assump_11
    intro assump_12
    apply True.intro


variable (p5 p7 p0 p2 p4 p3 p1 : Prop)
theorem file83_98415 : ((((((p3 ∧ p2) → (True ∨ p5)) ∨ ((p0 ∨ p7) ∧ (True ∧ p1))) ∨ (((p3 ∧ p1) ∨ (p4 → False)) → ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p3 ∧ p2) → (True ∨ p5)) ∨ ((p0 ∨ p7) ∧ (True ∧ p1))) ∨ (((p3 ∧ p1) ∨ (p4 → False)) → ((p3 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p0 p3 p4 p7 : Prop)
theorem file83_98983 : (((((p4 → False) ∨ (p0 ∨ p7)) ∧ ((p3 ∧ False) ∧ (p4 → p1))) → (((p0 → False) → (p4 → False)) → False)) ∨ ((((p1 ∨ p7) ∨ (p7 ∧ True)) → False) → False)) := by
  apply Or.inl
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
          apply False.elim assump_18
    case inr assump_12 =>
      cases assump_12
      case inl assump_23 =>
        cases assump_10
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply False.elim assump_30
      case inr assump_24 =>
        cases assump_10
        case intro assump_37 assump_38 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            apply False.elim assump_40


variable (p0 p1 p2 p5 p4 p7 : Prop)
theorem file83_99966 : ((((((p0 → False) ∧ (False → False)) → ((True ∧ True) ∧ (p7 ∧ p0))) → False) ∧ ((((p1 → p7) ∧ (True ∧ True)) ∧ ((p2 ∨ p2) ∧ (True → False))) ∨ (((p7 → True) ∧ (p4 ∧ p0)) ∧ ((p1 → p0) ∧ (False → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                have assump_85 : True := by
                  apply True.intro
                let assump_28 := assump_21 assump_85
                apply False.elim assump_28
              case inr assump_23 =>
                have assump_86 : True := by
                  apply True.intro
                let assump_36 := assump_21 assump_86
                apply False.elim assump_36
    case inr assump_7 =>
      cases assump_7
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_43
          case intro assump_46 assump_47 =>
            cases assump_41
            case intro assump_52 assump_53 =>
              have assump_87 : (((p0 → False) ∧ (False → False)) → ((True ∧ True) ∧ (p7 ∧ p0))) := by
                intro assump_64
                apply And.intro
                apply And.intro
                apply True.intro
                apply True.intro
                apply And.intro
                cases assump_64
                case intro assump_65 assump_66 =>
                  have assump_88 : p0 := by
                    exact assump_47
                  let assump_72 := assump_65 assump_88
                  apply False.elim assump_72
                cases assump_64
                case intro assump_76 assump_77 =>
                  exact assump_47
              let assump_63 := assump_2 assump_87
              apply False.elim assump_63


variable (p5 p7 p4 p2 p3 p1 : Prop)
theorem file83_102135 : (((((True ∨ p2) → (p3 ∧ p5)) → ((p2 → False) ∧ (p7 ∨ p4))) → (((p5 → False) → False) → ((False ∧ p5) → (p5 → False)))) ∨ ((((True → p1) ∧ (p3 → p7)) → ((False ∧ p1) ∨ (False → p1))) ∧ (((True → True) → (p7 ∨ p3)) ∧ ((p3 ∨ p1) → (p7 ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    apply False.elim assump_7


variable (p0 p6 p1 p5 p3 : Prop)
theorem file83_102604 : ((((((p3 → False) ∧ (p5 ∨ p6)) → ((p3 ∨ p1) → (p1 ∨ p0))) ∨ (((p0 → False) ∨ (p1 ∨ p3)) → False)) → False) → False) := by
  intro assump_12
  have assump_57 : ((((p3 → False) ∧ (p5 ∨ p6)) → ((p3 ∨ p1) → (p1 ∨ p0))) ∨ (((p0 → False) ∨ (p1 ∨ p3)) → False)) := by
    apply Or.inl
    intro assump_16
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      cases assump_16
      case intro assump_22 assump_23 =>
        cases assump_23
        case inl assump_26 =>
          have assump_58 : p3 := by
            exact assump_18
          let assump_31 := assump_22 assump_58
          apply False.elim assump_31
        case inr assump_27 =>
          have assump_59 : p3 := by
            exact assump_18
          let assump_38 := assump_22 assump_59
          apply False.elim assump_38
    case inr assump_19 =>
      cases assump_16
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          apply Or.inl
          exact assump_19
        case inr assump_49 =>
          apply Or.inl
          exact assump_19
  let assump_15 := assump_12 assump_57
  apply False.elim assump_15


variable (p7 p1 p6 p0 p5 p2 : Prop)
theorem file83_103808 : ((((((p1 ∧ True) ∧ (p7 ∧ p6)) ∧ ((p5 → False) ∧ (p5 ∨ p5))) → False) → ((((p1 → p5) → (True ∨ p2)) ∨ ((p0 → False) ∨ (p2 → False))) → False)) → False) := by
  intro assump_1
  have assump_49 : ((((p1 ∧ True) ∧ (p7 ∧ p6)) ∧ ((p5 → False) ∧ (p5 ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_23
              case inl assump_26 =>
                have assump_50 : p5 := by
                  exact assump_26
                let assump_31 := assump_22 assump_50
                apply False.elim assump_31
              case inr assump_27 =>
                have assump_51 : p5 := by
                  exact assump_27
                let assump_38 := assump_22 assump_51
                apply False.elim assump_38
  let assump_4 := assump_1 assump_49
  have assump_52 : (((p1 → p5) → (True ∨ p2)) ∨ ((p0 → False) ∨ (p2 → False))) := by
    apply Or.inl
    intro assump_43
    apply Or.inl
    apply True.intro
  let assump_42 := assump_4 assump_52
  apply False.elim assump_42


variable (p1 p7 p4 p2 p3 p5 : Prop)
theorem file83_105184 : (((((False → True) ∨ (p2 ∧ p5)) → False) → (((p1 ∧ p1) → (p4 ∧ p4)) ∨ ((p3 ∨ p5) ∨ (p2 ∨ False)))) ∨ ((((False → p5) → False) → ((p7 → p3) → False)) → False)) := by
  apply Or.inl
  intro assump_7
  apply Or.inl
  intro assump_10
  apply And.intro
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_37 : ((False → True) ∨ (p2 ∧ p5)) := by
      apply Or.inl
      intro assump_20
      apply True.intro
    let assump_19 := assump_7 assump_37
    apply False.elim assump_19
  cases assump_10
  case intro assump_24 assump_25 =>
    have assump_38 : ((False → True) ∨ (p2 ∧ p5)) := by
      apply Or.inl
      intro assump_33
      apply True.intro
    let assump_32 := assump_7 assump_38
    apply False.elim assump_32


variable (p7 p1 p6 p0 p2 p4 : Prop)
theorem file83_105982 : ((((((True → p2) → (p7 → False)) → False) → (((p6 → False) → False) ∨ ((p6 ∧ False) ∨ (p1 → False)))) ∧ ((((p6 ∨ p4) → False) ∧ ((p1 ∨ p1) ∧ (p4 ∧ False))) ∧ (((p6 → p4) ∨ (p2 ∨ p7)) ∧ ((p7 ∧ p0) ∨ (p4 ∨ p1))))) → False) := by
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
            cases assump_13
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
          case inr assump_15 =>
            cases assump_13
            case intro assump_26 assump_27 =>
              apply False.elim assump_27


variable (p3 p7 p2 p1 p4 : Prop)
theorem file83_106833 : ((((((True → False) ∧ (p1 ∨ p3)) → ((p4 ∧ p3) → False)) → (((p2 ∧ p4) → (p7 → False)) → False)) ∧ ((((p7 ∧ False) ∧ (p1 → False)) → ((p4 ∨ p2) ∨ (p2 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p7 ∧ False) ∧ (p1 → False)) → ((p4 ∨ p2) ∨ (p2 ∧ p2))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p3 p1 p7 p6 p2 : Prop)
theorem file83_107479 : ((((((p7 → p3) → False) → ((p2 ∧ False) → (p3 ∧ p1))) ∨ (((p3 ∨ p7) ∧ (p7 → False)) ∧ ((p2 → p7) ∨ (p6 → False)))) → False) → False) := by
  intro assump_5
  have assump_26 : ((((p7 → p3) → False) → ((p2 ∧ False) → (p3 ∧ p1))) ∨ (((p3 ∨ p7) ∧ (p7 → False)) ∧ ((p2 → p7) ∨ (p6 → False)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply And.intro
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
    cases assump_10
    case intro assump_17 assump_18 =>
      apply False.elim assump_18
  let assump_8 := assump_5 assump_26
  apply False.elim assump_8


variable (p1 p6 p7 p0 p5 p3 : Prop)
theorem file83_108156 : (((((True ∧ p5) ∨ (p1 ∧ p3)) ∧ ((p7 ∨ p6) ∧ (False ∧ p5))) → False) ∨ ((((p1 → p6) → (True ∧ p0)) → False) ∨ (((True → p0) → (p5 → False)) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
          case inr assump_15 =>
            cases assump_13
            case intro assump_24 assump_25 =>
              apply False.elim assump_24
    case inr assump_5 =>
      cases assump_5
      case intro assump_28 assump_29 =>
        cases assump_3
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


variable (p2 p3 p4 p5 p1 : Prop)
theorem file83_109428 : ((((((p3 ∨ p2) ∨ (p5 ∧ p4)) → False) ∨ (((False → False) → False) → False)) ∧ ((((False → p5) → (p5 → False)) ∧ ((p1 → True) → False)) ∧ (((p5 → False) → (p5 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_58 : ((p5 → False) → (p5 → False)) := by
            intro assump_19
            intro assump_20
            have assump_59 : p5 := by
              exact assump_20
            let assump_25 := assump_19 assump_59
            apply False.elim assump_25
          let assump_18 := assump_9 assump_58
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          have assump_60 : ((p5 → False) → (p5 → False)) := by
            intro assump_45
            intro assump_46
            have assump_61 : p5 := by
              exact assump_46
            let assump_51 := assump_45 assump_61
            apply False.elim assump_51
          let assump_44 := assump_35 assump_60
          apply False.elim assump_44


variable (p7 p4 p2 : Prop)
theorem file83_110778 : (((((p2 → False) ∨ (p4 ∨ False)) → ((p7 ∨ True) ∨ (True ∨ p2))) → False) → False) := by
  intro assump_10
  have assump_28 : (((p2 → False) ∨ (p4 ∨ False)) → ((p7 ∨ True) ∨ (True ∨ p2))) := by
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_16 =>
      cases assump_16
      case inl assump_19 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_20 =>
        apply False.elim assump_20
  let assump_13 := assump_10 assump_28
  apply False.elim assump_13


variable (p3 p5 p6 p2 : Prop)
theorem file83_111426 : ((((((p6 → False) ∨ (p2 → False)) ∧ ((False ∧ p3) ∧ (p5 ∨ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p6 → False) ∨ (p2 → False)) ∧ ((False ∧ p3) ∧ (p5 ∨ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
      case inr assump_9 =>
        cases assump_7
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p0 p7 p2 p6 p3 p5 p1 : Prop)
theorem file83_112261 : (((((p5 ∨ p3) ∨ (p1 ∧ p1)) ∨ ((p7 → True) ∨ (False ∧ p7))) → (((p1 → False) → (p0 ∧ False)) → ((p0 ∧ p2) → (True ∨ p1)))) ∨ ((((p6 ∨ p3) → (p2 → p5)) ∧ ((p7 → p2) ∧ (False → p5))) → False)) := by
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_9
    case inl assump_20 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case inl assump_24 =>
          apply Or.inl
          apply True.intro
        case inr assump_25 =>
          apply Or.inl
          apply True.intro
      case inr assump_23 =>
        cases assump_23
        case intro assump_30 assump_31 =>
          apply Or.inl
          apply True.intro
    case inr assump_21 =>
      cases assump_21
      case inl assump_36 =>
        apply Or.inl
        apply True.intro
      case inr assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          apply False.elim assump_40


variable (p4 p5 p3 p2 : Prop)
theorem file83_113309 : (((((p2 → False) → False) ∨ ((p4 ∧ p4) ∧ (False → p3))) ∧ (((False → False) ∨ (p5 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : ((False → False) ∨ (p5 → False)) := by
        apply Or.inl
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          have assump_37 : ((False → False) ∨ (p5 → False)) := by
            apply Or.inl
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_3 assump_37
          apply False.elim assump_29


variable (p7 p2 p6 : Prop)
theorem file83_114199 : (((((True ∨ p2) ∨ (p6 → False)) ∨ ((p2 ∧ p7) → (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p2) ∨ (p6 → False)) ∨ ((p2 ∧ p7) → (p6 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p1 p7 p2 p0 p3 : Prop)
theorem file83_114582 : ((((((p7 → False) ∨ (p0 ∧ p0)) ∨ ((p2 ∨ p7) ∧ (p2 ∧ p7))) ∧ (((True → p3) ∧ (False ∨ p6)) ∧ ((p7 → False) → False))) ∧ ((((True → False) ∧ (p1 ∨ p0)) → False) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_27
      case inl assump_29 =>
        cases assump_29
        case inl assump_31 =>
          cases assump_28
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              cases assump_38
              case inl assump_41 =>
                apply False.elim assump_41
              case inr assump_42 =>
                have assump_225 : (((True → False) ∧ (p1 ∨ p0)) → False) := by
                  intro assump_52
                  cases assump_52
                  case intro assump_53 assump_54 =>
                    cases assump_54
                    case inl assump_57 =>
                      have assump_226 : True := by
                        apply True.intro
                      let assump_62 := assump_53 assump_226
                      apply False.elim assump_62
                    case inr assump_58 =>
                      have assump_227 : True := by
                        apply True.intro
                      let assump_69 := assump_53 assump_227
                      apply False.elim assump_69
                let assump_51 := assump_26 assump_225
                apply False.elim assump_51
        case inr assump_32 =>
          cases assump_32
          case intro assump_76 assump_77 =>
            cases assump_28
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                cases assump_85
                case inl assump_88 =>
                  apply False.elim assump_88
                case inr assump_89 =>
                  have assump_228 : (((True → False) ∧ (p1 ∨ p0)) → False) := by
                    intro assump_99
                    cases assump_99
                    case intro assump_100 assump_101 =>
                      cases assump_101
                      case inl assump_104 =>
                        have assump_229 : True := by
                          apply True.intro
                        let assump_109 := assump_100 assump_229
                        apply False.elim assump_109
                      case inr assump_105 =>
                        have assump_230 : True := by
                          apply True.intro
                        let assump_116 := assump_100 assump_230
                        apply False.elim assump_116
                  let assump_98 := assump_26 assump_228
                  apply False.elim assump_98
      case inr assump_30 =>
        cases assump_30
        case intro assump_123 assump_124 =>
          cases assump_123
          case inl assump_125 =>
            cases assump_124
            case intro assump_129 assump_130 =>
              cases assump_28
              case intro assump_135 assump_136 =>
                cases assump_135
                case intro assump_137 assump_138 =>
                  cases assump_138
                  case inl assump_141 =>
                    apply False.elim assump_141
                  case inr assump_142 =>
                    have assump_231 : (((True → False) ∧ (p1 ∨ p0)) → False) := by
                      intro assump_152
                      cases assump_152
                      case intro assump_153 assump_154 =>
                        cases assump_154
                        case inl assump_157 =>
                          have assump_232 : True := by
                            apply True.intro
                          let assump_162 := assump_153 assump_232
                          apply False.elim assump_162
                        case inr assump_158 =>
                          have assump_233 : True := by
                            apply True.intro
                          let assump_169 := assump_153 assump_233
                          apply False.elim assump_169
                    let assump_151 := assump_26 assump_231
                    apply False.elim assump_151
          case inr assump_126 =>
            cases assump_124
            case intro assump_178 assump_179 =>
              cases assump_28
              case intro assump_184 assump_185 =>
                cases assump_184
                case intro assump_186 assump_187 =>
                  cases assump_187
                  case inl assump_190 =>
                    apply False.elim assump_190
                  case inr assump_191 =>
                    have assump_234 : (((True → False) ∧ (p1 ∨ p0)) → False) := by
                      intro assump_201
                      cases assump_201
                      case intro assump_202 assump_203 =>
                        cases assump_203
                        case inl assump_206 =>
                          have assump_235 : True := by
                            apply True.intro
                          let assump_211 := assump_202 assump_235
                          apply False.elim assump_211
                        case inr assump_207 =>
                          have assump_236 : True := by
                            apply True.intro
                          let assump_218 := assump_202 assump_236
                          apply False.elim assump_218
                    let assump_200 := assump_26 assump_234
                    apply False.elim assump_200


variable (p0 p5 p1 p2 p6 p4 p7 p3 : Prop)
theorem file83_120246 : (((((False ∧ p0) → (p0 → p4)) ∨ ((p2 ∧ p0) → False)) ∨ (((p5 → False) → False) ∧ ((False → p3) ∨ (p2 ∧ p6)))) ∨ ((((p7 ∧ p2) ∨ (p1 ∨ p5)) ∨ ((p7 → True) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p1 p7 p3 p2 p0 : Prop)
theorem file83_120642 : (((((p3 → p0) → (p2 ∧ p7)) → ((p3 ∧ p1) ∨ (p2 → True))) → False) → False) := by
  intro assump_5
  have assump_16 : (((p3 → p0) → (p2 ∧ p7)) → ((p3 ∧ p1) ∨ (p2 → True))) := by
    intro assump_9
    apply Or.inr
    intro assump_12
    apply True.intro
  let assump_8 := assump_5 assump_16
  apply False.elim assump_8


variable (p3 p6 p0 p4 p2 p7 : Prop)
theorem file83_121020 : ((((((p6 ∨ True) → (p4 ∧ p7)) → ((p2 ∧ False) ∨ (p4 → p4))) → False) ∧ ((((p3 ∧ p3) ∨ (p7 ∧ True)) ∧ ((p0 ∨ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p6 ∨ True) → (p4 ∧ p7)) → ((p2 ∧ False) ∨ (p4 → p4))) := by
      intro assump_10
      apply Or.inr
      intro assump_13
      exact assump_13
    let assump_9 := assump_2 assump_19
    apply False.elim assump_9


variable (p2 p5 p7 p6 p3 p4 p1 : Prop)
theorem file83_121536 : (((((p6 ∨ False) ∨ (p5 → p1)) ∧ ((False → p7) → False)) → (((p2 → p2) → (p2 ∨ p1)) ∧ ((True → False) → (p5 ∨ True)))) ∨ ((((p3 → False) ∧ (False ∨ p3)) → False) ∧ (((p7 ∨ p4) ∨ (p2 ∨ p5)) ∨ ((p5 → False) ∨ (p4 → p1))))) := by
  apply Or.inl
  intro assump_7
  apply And.intro
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        have assump_60 : (False → p7) := by
          intro assump_22
          apply False.elim assump_22
        let assump_21 := assump_12 assump_60
        apply False.elim assump_21
      case inr assump_16 =>
        apply False.elim assump_16
    case inr assump_14 =>
      have assump_61 : (False → p7) := by
        intro assump_35
        apply False.elim assump_35
      let assump_34 := assump_12 assump_61
      apply False.elim assump_34
  intro assump_41
  cases assump_7
  case intro assump_44 assump_45 =>
    cases assump_44
    case inl assump_46 =>
      cases assump_46
      case inl assump_48 =>
        apply Or.inr
        apply True.intro
      case inr assump_49 =>
        apply False.elim assump_49
    case inr assump_47 =>
      apply Or.inr
      apply True.intro


variable (p2 : Prop)
theorem file83_122820 : ((((((False ∧ p2) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p2) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p2) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p5 p7 p6 p0 p4 p2 : Prop)
theorem file83_123357 : (((((p2 ∨ p4) → False) ∨ ((p7 ∨ p1) → False)) ∧ (((p2 ∨ p6) ∧ (True ∧ p1)) ∧ ((p2 ∧ True) ∧ (p5 → False)))) → ((((p6 ∨ p7) ∨ (p5 ∧ p5)) → False) → (((p0 ∨ p7) → False) ∧ ((p2 ∨ p6) ∧ (p1 → p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_19
              case intro assump_24 assump_25 =>
                cases assump_17
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    have assump_453 : (p2 ∨ p4) := by
                      apply Or.inl
                      exact assump_32
                    let assump_44 := assump_12 assump_453
                    apply False.elim assump_44
            case inr assump_21 =>
              cases assump_19
              case intro assump_50 assump_51 =>
                cases assump_17
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case intro assump_58 assump_59 =>
                    have assump_454 : (p2 ∨ p4) := by
                      apply Or.inl
                      exact assump_58
                    let assump_70 := assump_12 assump_454
                    apply False.elim assump_70
      case inr assump_13 =>
        cases assump_11
        case intro assump_76 assump_77 =>
          cases assump_76
          case intro assump_78 assump_79 =>
            cases assump_78
            case inl assump_80 =>
              cases assump_79
              case intro assump_84 assump_85 =>
                cases assump_77
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    have assump_455 : (p7 ∨ p1) := by
                      apply Or.inr
                      exact assump_85
                    let assump_104 := assump_13 assump_455
                    apply False.elim assump_104
            case inr assump_81 =>
              cases assump_79
              case intro assump_110 assump_111 =>
                cases assump_77
                case intro assump_116 assump_117 =>
                  cases assump_116
                  case intro assump_118 assump_119 =>
                    have assump_456 : (p7 ∨ p1) := by
                      apply Or.inr
                      exact assump_111
                    let assump_130 := assump_13 assump_456
                    apply False.elim assump_130
  case inr assump_5 =>
    cases assump_1
    case intro assump_138 assump_139 =>
      cases assump_138
      case inl assump_140 =>
        cases assump_139
        case intro assump_144 assump_145 =>
          cases assump_144
          case intro assump_146 assump_147 =>
            cases assump_146
            case inl assump_148 =>
              cases assump_147
              case intro assump_152 assump_153 =>
                cases assump_145
                case intro assump_158 assump_159 =>
                  cases assump_158
                  case intro assump_160 assump_161 =>
                    have assump_457 : (p2 ∨ p4) := by
                      apply Or.inl
                      exact assump_160
                    let assump_172 := assump_140 assump_457
                    apply False.elim assump_172
            case inr assump_149 =>
              cases assump_147
              case intro assump_178 assump_179 =>
                cases assump_145
                case intro assump_184 assump_185 =>
                  cases assump_184
                  case intro assump_186 assump_187 =>
                    have assump_458 : (p2 ∨ p4) := by
                      apply Or.inl
                      exact assump_186
                    let assump_198 := assump_140 assump_458
                    apply False.elim assump_198
      case inr assump_141 =>
        cases assump_139
        case intro assump_204 assump_205 =>
          cases assump_204
          case intro assump_206 assump_207 =>
            cases assump_206
            case inl assump_208 =>
              cases assump_207
              case intro assump_212 assump_213 =>
                cases assump_205
                case intro assump_218 assump_219 =>
                  cases assump_218
                  case intro assump_220 assump_221 =>
                    have assump_459 : (p7 ∨ p1) := by
                      apply Or.inl
                      exact assump_5
                    let assump_232 := assump_141 assump_459
                    apply False.elim assump_232
            case inr assump_209 =>
              cases assump_207
              case intro assump_238 assump_239 =>
                cases assump_205
                case intro assump_244 assump_245 =>
                  cases assump_244
                  case intro assump_246 assump_247 =>
                    have assump_460 : (p7 ∨ p1) := by
                      apply Or.inl
                      exact assump_5
                    let assump_258 := assump_141 assump_460
                    apply False.elim assump_258
  apply And.intro
  cases assump_1
  case intro assump_264 assump_265 =>
    cases assump_264
    case inl assump_266 =>
      cases assump_265
      case intro assump_270 assump_271 =>
        cases assump_270
        case intro assump_272 assump_273 =>
          cases assump_272
          case inl assump_274 =>
            cases assump_273
            case intro assump_278 assump_279 =>
              cases assump_271
              case intro assump_284 assump_285 =>
                cases assump_284
                case intro assump_286 assump_287 =>
                  apply Or.inl
                  exact assump_286
          case inr assump_275 =>
            cases assump_273
            case intro assump_296 assump_297 =>
              cases assump_271
              case intro assump_302 assump_303 =>
                cases assump_302
                case intro assump_304 assump_305 =>
                  apply Or.inl
                  exact assump_304
    case inr assump_267 =>
      cases assump_265
      case intro assump_314 assump_315 =>
        cases assump_314
        case intro assump_316 assump_317 =>
          cases assump_316
          case inl assump_318 =>
            cases assump_317
            case intro assump_322 assump_323 =>
              cases assump_315
              case intro assump_328 assump_329 =>
                cases assump_328
                case intro assump_330 assump_331 =>
                  apply Or.inl
                  exact assump_330
          case inr assump_319 =>
            cases assump_317
            case intro assump_340 assump_341 =>
              cases assump_315
              case intro assump_346 assump_347 =>
                cases assump_346
                case intro assump_348 assump_349 =>
                  apply Or.inl
                  exact assump_348
  intro assump_356
  cases assump_1
  case intro assump_361 assump_362 =>
    cases assump_361
    case inl assump_363 =>
      cases assump_362
      case intro assump_367 assump_368 =>
        cases assump_367
        case intro assump_369 assump_370 =>
          cases assump_369
          case inl assump_371 =>
            cases assump_370
            case intro assump_375 assump_376 =>
              cases assump_368
              case intro assump_381 assump_382 =>
                cases assump_381
                case intro assump_383 assump_384 =>
                  exact assump_383
          case inr assump_372 =>
            cases assump_370
            case intro assump_393 assump_394 =>
              cases assump_368
              case intro assump_399 assump_400 =>
                cases assump_399
                case intro assump_401 assump_402 =>
                  exact assump_401
    case inr assump_364 =>
      cases assump_362
      case intro assump_411 assump_412 =>
        cases assump_411
        case intro assump_413 assump_414 =>
          cases assump_413
          case inl assump_415 =>
            cases assump_414
            case intro assump_419 assump_420 =>
              cases assump_412
              case intro assump_425 assump_426 =>
                cases assump_425
                case intro assump_427 assump_428 =>
                  exact assump_427
          case inr assump_416 =>
            cases assump_414
            case intro assump_437 assump_438 =>
              cases assump_412
              case intro assump_443 assump_444 =>
                cases assump_443
                case intro assump_445 assump_446 =>
                  exact assump_445


variable (p3 p7 p4 p5 p2 p1 p6 : Prop)
theorem file83_132413 : (((((p2 ∧ p4) ∧ (False → False)) → ((p5 ∨ p6) ∨ (p3 → p4))) → False) → ((((False → p6) ∧ (p3 → True)) ∧ ((True → p6) ∨ (True → p1))) ∧ (((p7 ∨ False) ∨ (p7 ∨ True)) → ((True ∨ p2) ∨ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  apply True.intro
  apply Or.inl
  intro assump_8
  have assump_50 : (((p2 ∧ p4) ∧ (False → False)) → ((p5 ∨ p6) ∨ (p3 → p4))) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply Or.inr
        intro assump_23
        exact assump_16
  let assump_11 := assump_1 assump_50
  apply False.elim assump_11
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case inl assump_32 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_33 =>
      apply False.elim assump_33
  case inr assump_31 =>
    cases assump_31
    case inl assump_40 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_41 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p5 p1 p2 p4 p3 p0 : Prop)
theorem file83_133665 : (((((p1 → False) ∨ (p2 → False)) ∧ ((p4 → True) ∨ (True → False))) ∧ (((p0 → False) → (p2 → True)) → False)) → ((((p3 → p4) ∧ (p2 → False)) ∧ ((True → False) ∧ (p4 ∧ p0))) ∧ (((False → False) ∨ (p1 → p4)) ∨ ((p4 → False) → (True → p5))))) := by
  intro assump_16
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_17
  cases assump_16
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_23
        case inl assump_28 =>
          have assump_338 : ((p0 → False) → (p2 → True)) := by
            intro assump_35
            intro assump_36
            apply True.intro
          let assump_34 := assump_21 assump_338
          apply False.elim assump_34
        case inr assump_29 =>
          have assump_339 : ((p0 → False) → (p2 → True)) := by
            intro assump_45
            intro assump_46
            apply True.intro
          let assump_44 := assump_21 assump_339
          apply False.elim assump_44
      case inr assump_25 =>
        cases assump_23
        case inl assump_52 =>
          have assump_340 : ((p0 → False) → (p2 → True)) := by
            intro assump_59
            intro assump_60
            apply True.intro
          let assump_58 := assump_21 assump_340
          apply False.elim assump_58
        case inr assump_53 =>
          have assump_341 : ((p0 → False) → (p2 → True)) := by
            intro assump_69
            intro assump_70
            apply True.intro
          let assump_68 := assump_21 assump_341
          apply False.elim assump_68
  intro assump_74
  cases assump_16
  case intro assump_77 assump_78 =>
    cases assump_77
    case intro assump_79 assump_80 =>
      cases assump_79
      case inl assump_81 =>
        cases assump_80
        case inl assump_85 =>
          have assump_342 : ((p0 → False) → (p2 → True)) := by
            intro assump_92
            intro assump_93
            apply True.intro
          let assump_91 := assump_78 assump_342
          apply False.elim assump_91
        case inr assump_86 =>
          have assump_343 : ((p0 → False) → (p2 → True)) := by
            intro assump_102
            intro assump_103
            apply True.intro
          let assump_101 := assump_78 assump_343
          apply False.elim assump_101
      case inr assump_82 =>
        cases assump_80
        case inl assump_109 =>
          have assump_344 : ((p0 → False) → (p2 → True)) := by
            intro assump_116
            intro assump_117
            apply True.intro
          let assump_115 := assump_78 assump_344
          apply False.elim assump_115
        case inr assump_110 =>
          have assump_345 : ((p0 → False) → (p2 → True)) := by
            intro assump_126
            intro assump_127
            apply True.intro
          let assump_125 := assump_78 assump_345
          apply False.elim assump_125
  apply And.intro
  intro assump_131
  cases assump_16
  case intro assump_134 assump_135 =>
    cases assump_134
    case intro assump_136 assump_137 =>
      cases assump_136
      case inl assump_138 =>
        cases assump_137
        case inl assump_142 =>
          have assump_346 : ((p0 → False) → (p2 → True)) := by
            intro assump_149
            intro assump_150
            apply True.intro
          let assump_148 := assump_135 assump_346
          apply False.elim assump_148
        case inr assump_143 =>
          have assump_347 : ((p0 → False) → (p2 → True)) := by
            intro assump_159
            intro assump_160
            apply True.intro
          let assump_158 := assump_135 assump_347
          apply False.elim assump_158
      case inr assump_139 =>
        cases assump_137
        case inl assump_166 =>
          have assump_348 : ((p0 → False) → (p2 → True)) := by
            intro assump_173
            intro assump_174
            apply True.intro
          let assump_172 := assump_135 assump_348
          apply False.elim assump_172
        case inr assump_167 =>
          have assump_349 : ((p0 → False) → (p2 → True)) := by
            intro assump_183
            intro assump_184
            apply True.intro
          let assump_182 := assump_135 assump_349
          apply False.elim assump_182
  apply And.intro
  cases assump_16
  case intro assump_188 assump_189 =>
    cases assump_188
    case intro assump_190 assump_191 =>
      cases assump_190
      case inl assump_192 =>
        cases assump_191
        case inl assump_196 =>
          have assump_350 : ((p0 → False) → (p2 → True)) := by
            intro assump_203
            intro assump_204
            apply True.intro
          let assump_202 := assump_189 assump_350
          apply False.elim assump_202
        case inr assump_197 =>
          have assump_351 : ((p0 → False) → (p2 → True)) := by
            intro assump_213
            intro assump_214
            apply True.intro
          let assump_212 := assump_189 assump_351
          apply False.elim assump_212
      case inr assump_193 =>
        cases assump_191
        case inl assump_220 =>
          have assump_352 : ((p0 → False) → (p2 → True)) := by
            intro assump_227
            intro assump_228
            apply True.intro
          let assump_226 := assump_189 assump_352
          apply False.elim assump_226
        case inr assump_221 =>
          have assump_353 : ((p0 → False) → (p2 → True)) := by
            intro assump_237
            intro assump_238
            apply True.intro
          let assump_236 := assump_189 assump_353
          apply False.elim assump_236
  cases assump_16
  case intro assump_242 assump_243 =>
    cases assump_242
    case intro assump_244 assump_245 =>
      cases assump_244
      case inl assump_246 =>
        cases assump_245
        case inl assump_250 =>
          have assump_354 : ((p0 → False) → (p2 → True)) := by
            intro assump_257
            intro assump_258
            apply True.intro
          let assump_256 := assump_243 assump_354
          apply False.elim assump_256
        case inr assump_251 =>
          have assump_355 : ((p0 → False) → (p2 → True)) := by
            intro assump_267
            intro assump_268
            apply True.intro
          let assump_266 := assump_243 assump_355
          apply False.elim assump_266
      case inr assump_247 =>
        cases assump_245
        case inl assump_274 =>
          have assump_356 : ((p0 → False) → (p2 → True)) := by
            intro assump_281
            intro assump_282
            apply True.intro
          let assump_280 := assump_243 assump_356
          apply False.elim assump_280
        case inr assump_275 =>
          have assump_357 : ((p0 → False) → (p2 → True)) := by
            intro assump_291
            intro assump_292
            apply True.intro
          let assump_290 := assump_243 assump_357
          apply False.elim assump_290
  cases assump_16
  case intro assump_296 assump_297 =>
    cases assump_296
    case intro assump_298 assump_299 =>
      cases assump_298
      case inl assump_300 =>
        cases assump_299
        case inl assump_304 =>
          apply Or.inl
          apply Or.inl
          intro assump_310
          apply False.elim assump_310
        case inr assump_305 =>
          apply Or.inl
          apply Or.inl
          intro assump_317
          apply False.elim assump_317
      case inr assump_301 =>
        cases assump_299
        case inl assump_322 =>
          apply Or.inl
          apply Or.inl
          intro assump_328
          apply False.elim assump_328
        case inr assump_323 =>
          apply Or.inl
          apply Or.inl
          intro assump_335
          apply False.elim assump_335


variable (p0 p3 p4 p6 p5 : Prop)
theorem file83_141512 : ((((((p5 → False) → False) → False) ∧ (((p5 → False) → (p5 → p5)) ∨ ((p3 → False) → (p4 ∨ p3)))) ∧ ((((p5 → False) → False) → ((True ∧ p6) ∨ (p0 → p0))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        have assump_42 : (((p5 → False) → False) → ((True ∧ p6) ∨ (p0 → p0))) := by
          intro assump_19
          apply Or.inr
          intro assump_22
          exact assump_22
        let assump_18 := assump_7 assump_42
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_43 : (((p5 → False) → False) → ((True ∧ p6) ∨ (p0 → p0))) := by
          intro assump_33
          apply Or.inr
          intro assump_36
          exact assump_36
        let assump_32 := assump_7 assump_43
        apply False.elim assump_32


variable (p2 p3 p5 p0 : Prop)
theorem file83_142472 : ((((((p0 ∨ p2) → False) ∧ ((False ∨ p3) ∧ (True ∧ p0))) → (((False → False) → False) → ((p0 ∧ p3) ∧ (p5 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_76 : ((((p0 ∨ p2) → False) ∧ ((False ∨ p3) ∧ (True ∧ p0))) → (((False → False) → False) → ((p0 ∧ p3) ∧ (p5 ∨ p5)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            exact assump_22
    cases assump_5
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        cases assump_33
        case inl assump_35 =>
          apply False.elim assump_35
        case inr assump_36 =>
          cases assump_34
          case intro assump_41 assump_42 =>
            exact assump_36
    cases assump_5
    case intro assump_49 assump_50 =>
      cases assump_50
      case intro assump_53 assump_54 =>
        cases assump_53
        case inl assump_55 =>
          apply False.elim assump_55
        case inr assump_56 =>
          cases assump_54
          case intro assump_61 assump_62 =>
            have assump_77 : (p0 ∨ p2) := by
              apply Or.inl
              exact assump_62
            let assump_69 := assump_49 assump_77
            apply False.elim assump_69
  let assump_4 := assump_1 assump_76
  apply False.elim assump_4


variable (p1 p2 p0 p6 p3 : Prop)
theorem file83_144137 : (((((p6 ∨ True) ∨ (p0 ∧ False)) → False) → (((p6 ∨ p6) → False) ∧ ((p6 ∧ p3) → (True → True)))) ∨ ((((p6 ∨ p1) ∨ (p0 ∧ True)) ∧ ((p0 ∨ p2) ∨ (p1 ∧ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_23 : ((p6 ∨ True) ∨ (p0 ∧ False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_3
    let assump_9 := assump_1 assump_23
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_24 : ((p6 ∨ True) ∨ (p0 ∧ False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_4
    let assump_17 := assump_1 assump_24
    apply False.elim assump_17
  intro assump_21
  intro assump_22
  apply True.intro


variable (p5 p4 p6 p2 p1 p7 p3 : Prop)
theorem file83_144924 : (((((p4 ∨ True) ∨ (False → False)) → False) ∧ (((p2 → False) → (p5 → p7)) ∧ ((True ∧ p3) ∨ (p7 ∧ p1)))) → ((((True ∨ p7) → False) → False) → (((True ∨ True) → (p6 ∨ True)) ∨ ((p1 → p5) → (p5 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_21
          cases assump_21
          case inl assump_22 =>
            apply Or.inr
            apply True.intro
          case inr assump_23 =>
            apply Or.inr
            apply True.intro
      case inr assump_14 =>
        cases assump_14
        case intro assump_28 assump_29 =>
          apply Or.inl
          intro assump_34
          cases assump_34
          case inl assump_35 =>
            apply Or.inr
            apply True.intro
          case inr assump_36 =>
            apply Or.inr
            apply True.intro


variable (p7 p2 p3 p6 p1 : Prop)
theorem file83_146033 : (((((p3 → p3) ∨ (p2 ∧ p2)) → False) ∧ (((p2 ∧ p6) → False) ∧ ((True ∨ p7) ∧ (p1 ∨ p2)))) → False) := by
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
          case inl assump_16 =>
            have assump_68 : ((p3 → p3) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              intro assump_23
              exact assump_23
            let assump_22 := assump_2 assump_68
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_69 : ((p3 → p3) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              intro assump_34
              exact assump_34
            let assump_33 := assump_2 assump_69
            apply False.elim assump_33
        case inr assump_13 =>
          cases assump_11
          case inl assump_42 =>
            have assump_70 : ((p3 → p3) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              intro assump_50
              exact assump_50
            let assump_49 := assump_2 assump_70
            apply False.elim assump_49
          case inr assump_43 =>
            have assump_71 : ((p3 → p3) ∨ (p2 ∧ p2)) := by
              apply Or.inl
              intro assump_62
              exact assump_62
            let assump_61 := assump_2 assump_71
            apply False.elim assump_61


variable (p5 p3 p2 p0 p6 p7 : Prop)
theorem file83_147577 : ((((((p3 ∨ p7) ∧ (p5 ∨ p0)) ∨ ((p5 → True) ∨ (p6 ∧ False))) ∧ (((False → False) → False) → ((p2 → p7) → (p3 → False)))) → False) → False) := by
  intro assump_69
  have assump_93 : ((((p3 ∨ p7) ∧ (p5 ∨ p0)) ∨ ((p5 → True) ∨ (p6 ∧ False))) ∧ (((False → False) → False) → ((p2 → p7) → (p3 → False)))) := by
    apply And.intro
    apply Or.inr
    apply Or.inl
    intro assump_73
    apply True.intro
    intro assump_74
    intro assump_75
    intro assump_76
    have assump_94 : (False → False) := by
      intro assump_84
      apply False.elim assump_84
    let assump_83 := assump_74 assump_94
    apply False.elim assump_83
  let assump_72 := assump_69 assump_93
  apply False.elim assump_72


variable (p7 p4 p0 p2 p1 p3 : Prop)
theorem file83_148335 : (((((p0 → False) → False) ∨ ((p7 → p3) ∨ (p4 → p1))) → False) → ((((p4 → False) ∧ (False ∧ False)) → ((p2 → False) → False)) ∨ (((p0 → False) → False) ∨ ((p0 ∧ p4) → False)))) := by
  intro assump_39
  apply Or.inl
  intro assump_42
  intro assump_43
  cases assump_42
  case intro assump_46 assump_47 =>
    cases assump_47
    case intro assump_50 assump_51 =>
      apply False.elim assump_50


variable (p0 p4 p2 p5 p6 : Prop)
theorem file83_148788 : (((((True → False) → (True ∧ p0)) → False) → False) ∧ ((((p5 ∧ p6) → (p4 → False)) ∧ ((True → True) ∧ (p5 → True))) → (((True ∧ p2) → (False → False)) ∨ ((p4 ∧ p4) ∨ (p0 ∧ p4))))) := by
  apply And.intro
  intro assump_1
  have assump_30 : ((True → False) → (True ∧ p0)) := by
    intro assump_5
    apply And.intro
    apply True.intro
    have assump_31 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_31
    apply False.elim assump_8
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_17
    case intro assump_20 assump_21 =>
      apply Or.inl
      intro assump_26
      intro assump_27
      apply False.elim assump_27


variable (p6 p0 p2 p5 p3 p4 p1 : Prop)
theorem file83_149603 : (((((p1 ∧ False) ∧ (p1 ∨ p5)) → False) ∨ (((p2 ∧ p0) → (False ∨ p4)) ∧ ((p4 ∧ p4) → False))) ∨ ((((p3 ∧ p4) ∨ (False → p2)) ∧ ((p6 → False) ∧ (p1 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_5


variable (p6 p5 p3 p4 p0 p2 : Prop)
theorem file83_150021 : ((((((p5 ∧ False) → (True ∨ p6)) ∨ ((p6 → p4) ∧ (False ∨ p4))) ∨ (((p6 ∧ p0) → False) ∨ ((True → p3) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∧ False) → (True ∨ p6)) ∨ ((p6 → p4) ∧ (False ∨ p4))) ∨ (((p6 ∧ p0) → False) ∨ ((True → p3) → (p2 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


