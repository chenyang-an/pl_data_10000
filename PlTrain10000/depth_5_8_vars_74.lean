variable (p4 p6 p1 p5 p7 p3 p2 : Prop)
theorem file74_47 : (((((True ∧ p2) → False) → ((p2 → p4) ∨ (p5 ∨ True))) ∨ (((p2 → True) ∨ (p6 ∧ p5)) ∧ ((True ∨ p7) ∧ (p1 → p1)))) → ((((p1 → True) → (False ∨ p5)) ∨ ((p3 ∨ p2) ∧ (p4 ∧ p4))) → (((p6 → True) ∨ (p7 → p5)) ∨ ((p1 → False) ∧ (p3 → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_11
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              apply Or.inl
              intro assump_26
              apply True.intro
            case inr assump_21 =>
              apply Or.inl
              apply Or.inl
              intro assump_31
              apply True.intro
        case inr assump_15 =>
          cases assump_15
          case intro assump_32 assump_33 =>
            cases assump_13
            case intro assump_38 assump_39 =>
              cases assump_38
              case inl assump_40 =>
                apply Or.inl
                apply Or.inl
                intro assump_46
                apply True.intro
              case inr assump_41 =>
                apply Or.inl
                apply Or.inl
                intro assump_51
                apply True.intro
  case inr assump_4 =>
    cases assump_4
    case intro assump_52 assump_53 =>
      cases assump_52
      case inl assump_54 =>
        cases assump_53
        case intro assump_58 assump_59 =>
          cases assump_1
          case inl assump_64 =>
            apply Or.inl
            apply Or.inl
            intro assump_68
            apply True.intro
          case inr assump_65 =>
            cases assump_65
            case intro assump_69 assump_70 =>
              cases assump_69
              case inl assump_71 =>
                cases assump_70
                case intro assump_75 assump_76 =>
                  cases assump_75
                  case inl assump_77 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_83
                    apply True.intro
                  case inr assump_78 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_88
                    apply True.intro
              case inr assump_72 =>
                cases assump_72
                case intro assump_89 assump_90 =>
                  cases assump_70
                  case intro assump_95 assump_96 =>
                    cases assump_95
                    case inl assump_97 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_103
                      apply True.intro
                    case inr assump_98 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_108
                      apply True.intro
      case inr assump_55 =>
        cases assump_53
        case intro assump_111 assump_112 =>
          cases assump_1
          case inl assump_117 =>
            apply Or.inl
            apply Or.inl
            intro assump_121
            apply True.intro
          case inr assump_118 =>
            cases assump_118
            case intro assump_122 assump_123 =>
              cases assump_122
              case inl assump_124 =>
                cases assump_123
                case intro assump_128 assump_129 =>
                  cases assump_128
                  case inl assump_130 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_136
                    apply True.intro
                  case inr assump_131 =>
                    apply Or.inl
                    apply Or.inl
                    intro assump_141
                    apply True.intro
              case inr assump_125 =>
                cases assump_125
                case intro assump_142 assump_143 =>
                  cases assump_123
                  case intro assump_148 assump_149 =>
                    cases assump_148
                    case inl assump_150 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_156
                      apply True.intro
                    case inr assump_151 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_161
                      apply True.intro


variable (p0 p4 p2 p7 p1 p6 : Prop)
theorem file74_4786 : (((((p1 → p6) ∧ (p7 → False)) → ((p7 ∧ p1) ∧ (p4 → p1))) ∧ (((p7 → False) ∧ (False ∧ p0)) → ((p1 ∧ p2) ∧ (p1 → False)))) → ((((p1 ∨ True) → False) → False) ∨ (((p2 ∧ p2) ∨ (p4 ∧ p4)) ∨ ((p0 ∨ p2) ∨ (p4 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_15 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_8 assump_15
    apply False.elim assump_11


variable (p6 p1 p5 p7 p4 p3 p2 : Prop)
theorem file74_5325 : (((((p3 → False) → (p1 → True)) ∨ ((False → p7) → (p5 → False))) ∨ (((False → p6) ∧ (False ∧ p1)) ∧ ((True → False) ∨ (p7 ∨ p3)))) ∨ ((((True → p6) → False) → ((p1 ∧ p2) ∧ (p4 ∧ p6))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p6 p5 p3 p2 p1 p4 p7 p0 : Prop)
theorem file74_5689 : ((((((True → True) ∧ (p4 ∧ p4)) ∧ ((p6 → False) ∧ (p5 → False))) ∨ (((p7 → False) → (p6 ∧ True)) ∨ ((True ∨ True) → (True → p1)))) ∧ ((((p2 ∧ p3) → (p7 ∨ p6)) ∧ ((p4 → p4) → False)) ∨ (((p5 ∧ False) ∧ (p0 ∨ p1)) ∧ ((False → False) ∨ (p0 ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_3
              case inl assump_24 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  have assump_105 : (p4 → p4) := by
                    intro assump_33
                    exact assump_33
                  let assump_32 := assump_27 assump_105
                  apply False.elim assump_32
              case inr assump_25 =>
                cases assump_25
                case intro assump_39 assump_40 =>
                  cases assump_39
                  case intro assump_41 assump_42 =>
                    cases assump_41
                    case intro assump_43 assump_44 =>
                      apply False.elim assump_44
    case inr assump_5 =>
      cases assump_5
      case inl assump_49 =>
        cases assump_3
        case inl assump_53 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            have assump_106 : (p4 → p4) := by
              intro assump_62
              exact assump_62
            let assump_61 := assump_56 assump_106
            apply False.elim assump_61
        case inr assump_54 =>
          cases assump_54
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                apply False.elim assump_73
      case inr assump_50 =>
        cases assump_3
        case inl assump_80 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            have assump_107 : (p4 → p4) := by
              intro assump_89
              exact assump_89
            let assump_88 := assump_83 assump_107
            apply False.elim assump_88
        case inr assump_81 =>
          cases assump_81
          case intro assump_95 assump_96 =>
            cases assump_95
            case intro assump_97 assump_98 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                apply False.elim assump_100


variable (p4 p3 p7 p0 p2 p1 : Prop)
theorem file74_8432 : ((((((True → False) ∧ (True ∨ p4)) → ((p1 ∨ p7) ∨ (p2 ∧ p4))) ∨ (((False → False) → (p2 ∨ p7)) ∨ ((p1 → p3) → (p1 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True → False) ∧ (True ∨ p4)) → ((p1 ∨ p7) ∨ (p2 ∧ p4))) ∨ (((False → False) → (p2 ∨ p7)) ∨ ((p1 → p3) → (p1 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_29 : True := by
          apply True.intro
        let assump_14 := assump_6 assump_29
        apply False.elim assump_14
      case inr assump_11 =>
        have assump_30 : True := by
          apply True.intro
        let assump_21 := assump_6 assump_30
        apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p0 p2 p5 p7 p6 p3 p4 p1 : Prop)
theorem file74_9325 : (((((False ∧ False) → (False → p2)) → ((p7 ∧ p1) ∨ (False → False))) → (((p2 → False) → False) → ((p2 → p5) → (p6 → p6)))) ∨ ((((p5 → False) → False) → ((p4 → False) → (True ∨ p1))) ∨ (((p3 ∨ p6) ∨ (p6 ∧ p3)) ∧ ((p2 ∧ p6) ∧ (p7 → p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  exact assump_4


variable (p7 p3 p1 p6 p4 p2 : Prop)
theorem file74_9729 : (((((p7 → False) → (p6 ∧ p1)) ∧ ((p3 ∧ p1) → False)) ∧ (((p3 ∧ False) → False) → ((True ∨ False) → False))) → ((((p6 → p1) → (p6 → False)) → False) ∧ (((p6 ∨ p6) → (p4 ∧ p3)) ∧ ((p6 ∨ p2) ∨ (p7 ∨ False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_150 : ((p3 ∧ False) → False) := by
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      let assump_15 := assump_6 assump_150
      have assump_151 : (True ∨ False) := by
        apply Or.inl
        apply True.intro
      let assump_23 := assump_15 assump_151
      apply False.elim assump_23
  apply And.intro
  intro assump_27
  apply And.intro
  cases assump_27
  case inl assump_28 =>
    cases assump_1
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        have assump_152 : ((p3 ∧ False) → False) := by
          intro assump_43
          cases assump_43
          case intro assump_44 assump_45 =>
            apply False.elim assump_45
        let assump_42 := assump_33 assump_152
        have assump_153 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_50 := assump_42 assump_153
        apply False.elim assump_50
  case inr assump_29 =>
    cases assump_1
    case intro assump_56 assump_57 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        have assump_154 : ((p3 ∧ False) → False) := by
          intro assump_67
          cases assump_67
          case intro assump_68 assump_69 =>
            apply False.elim assump_69
        let assump_66 := assump_57 assump_154
        have assump_155 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_74 := assump_66 assump_155
        apply False.elim assump_74
  cases assump_27
  case inl assump_78 =>
    cases assump_1
    case intro assump_82 assump_83 =>
      cases assump_82
      case intro assump_84 assump_85 =>
        have assump_156 : ((p3 ∧ False) → False) := by
          intro assump_93
          cases assump_93
          case intro assump_94 assump_95 =>
            apply False.elim assump_95
        let assump_92 := assump_83 assump_156
        have assump_157 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_100 := assump_92 assump_157
        apply False.elim assump_100
  case inr assump_79 =>
    cases assump_1
    case intro assump_106 assump_107 =>
      cases assump_106
      case intro assump_108 assump_109 =>
        have assump_158 : ((p3 ∧ False) → False) := by
          intro assump_117
          cases assump_117
          case intro assump_118 assump_119 =>
            apply False.elim assump_119
        let assump_116 := assump_107 assump_158
        have assump_159 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_124 := assump_116 assump_159
        apply False.elim assump_124
  cases assump_1
  case intro assump_128 assump_129 =>
    cases assump_128
    case intro assump_130 assump_131 =>
      have assump_160 : ((p3 ∧ False) → False) := by
        intro assump_139
        cases assump_139
        case intro assump_140 assump_141 =>
          apply False.elim assump_141
      let assump_138 := assump_129 assump_160
      have assump_161 : (True ∨ False) := by
        apply Or.inl
        apply True.intro
      let assump_146 := assump_138 assump_161
      apply False.elim assump_146


variable (p3 p4 p2 p0 p6 p1 : Prop)
theorem file74_13404 : (((((False ∨ p3) ∧ (p2 ∧ p1)) ∧ ((p6 ∧ False) ∨ (p4 ∧ False))) ∧ (((True ∨ p3) → False) → False)) → ((((True ∨ p6) ∧ (p0 ∧ True)) → False) ∨ (((p6 → False) → (p2 ∨ False)) → False))) := by
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
          cases assump_7
          case intro assump_14 assump_15 =>
            cases assump_5
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_23
            case inr assump_21 =>
              cases assump_21
              case intro assump_28 assump_29 =>
                apply False.elim assump_29


variable (p2 p0 : Prop)
theorem file74_14346 : (((((True → False) ∧ (p2 ∧ p0)) → False) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → False) ∧ (p2 ∧ p0)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p7 p1 : Prop)
theorem file74_14885 : ((((((False → False) → False) → False) ∨ (((p7 ∨ p2) → False) ∨ ((p7 → False) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p7 ∨ p2) → False) ∨ ((p7 → False) ∧ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p5 p6 p3 p4 p0 : Prop)
theorem file74_15467 : (((((p2 → p4) ∨ (p5 ∨ p6)) ∧ ((True → p3) → (p6 ∨ p2))) ∧ (((True → False) → False) → False)) → ((((p0 → False) ∧ (p4 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        have assump_64 : ((True → False) → False) := by
          intro assump_18
          have assump_65 : True := by
            apply True.intro
          let assump_21 := assump_18 assump_65
          apply False.elim assump_21
        let assump_17 := assump_6 assump_64
        apply False.elim assump_17
      case inr assump_10 =>
        cases assump_10
        case inl assump_28 =>
          have assump_66 : ((True → False) → False) := by
            intro assump_37
            have assump_67 : True := by
              apply True.intro
            let assump_40 := assump_37 assump_67
            apply False.elim assump_40
          let assump_36 := assump_6 assump_66
          apply False.elim assump_36
        case inr assump_29 =>
          have assump_68 : ((True → False) → False) := by
            intro assump_54
            have assump_69 : True := by
              apply True.intro
            let assump_57 := assump_54 assump_69
            apply False.elim assump_57
          let assump_53 := assump_6 assump_68
          apply False.elim assump_53


variable (p0 p2 p4 p5 : Prop)
theorem file74_16942 : ((((((p2 ∨ False) → False) → ((p4 → True) → (p0 → True))) ∨ (((False → False) ∨ (True ∨ p5)) ∨ ((p2 ∧ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 ∨ False) → False) → ((p4 → True) → (p0 → True))) ∨ (((False → False) ∨ (True ∨ p5)) ∨ ((p2 ∧ p2) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p7 p2 : Prop)
theorem file74_17451 : (((((False → False) → False) → ((p7 ∧ p2) → (p7 → p4))) → False) → False) := by
  intro assump_1
  have assump_28 : (((False → False) → False) → ((p7 ∧ p2) → (p7 → p4))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_29 : (False → False) := by
        intro assump_19
        apply False.elim assump_19
      let assump_18 := assump_5 assump_29
      apply False.elim assump_18
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p3 p5 p6 p1 p4 p7 p2 p0 : Prop)
theorem file74_18051 : ((((((p6 ∧ p0) → False) → ((p7 ∨ p7) → (p2 → False))) ∨ (((p5 ∨ p7) → (p6 → p3)) ∧ ((p3 → False) ∧ (p2 ∨ p3)))) ∧ ((((p1 → False) ∧ (False ∧ p4)) ∨ ((p2 ∧ False) ∧ (p0 → p5))) ∧ (((False → False) ∧ (False ∨ p5)) → False))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case inl assump_22 =>
      cases assump_21
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            cases assump_31
            case intro assump_34 assump_35 =>
              apply False.elim assump_34
        case inr assump_29 =>
          cases assump_29
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              apply False.elim assump_41
    case inr assump_23 =>
      cases assump_23
      case intro assump_46 assump_47 =>
        cases assump_47
        case intro assump_50 assump_51 =>
          cases assump_51
          case inl assump_54 =>
            cases assump_21
            case intro assump_58 assump_59 =>
              cases assump_58
              case inl assump_60 =>
                cases assump_60
                case intro assump_62 assump_63 =>
                  cases assump_63
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_66
              case inr assump_61 =>
                cases assump_61
                case intro assump_70 assump_71 =>
                  cases assump_70
                  case intro assump_72 assump_73 =>
                    apply False.elim assump_73
          case inr assump_55 =>
            cases assump_21
            case intro assump_80 assump_81 =>
              cases assump_80
              case inl assump_82 =>
                cases assump_82
                case intro assump_84 assump_85 =>
                  cases assump_85
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_88
              case inr assump_83 =>
                cases assump_83
                case intro assump_92 assump_93 =>
                  cases assump_92
                  case intro assump_94 assump_95 =>
                    apply False.elim assump_95


variable (p0 p4 p7 p5 p6 p3 p1 p2 : Prop)
theorem file74_20445 : ((((((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) → False) ∧ ((((p4 ∧ True) → False) ∨ ((p5 ∨ p3) ∧ (p4 → True))) ∨ (((p0 ∧ True) → (p1 ∨ False)) ∨ ((p7 ∧ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_147 : (((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) := by
          intro assump_14
          intro assump_15
          cases assump_14
          case inl assump_18 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inr
              apply True.intro
            case inr assump_21 =>
              apply Or.inr
              apply True.intro
          case inr assump_19 =>
            cases assump_19
            case inl assump_26 =>
              apply Or.inr
              apply True.intro
            case inr assump_27 =>
              apply Or.inr
              apply True.intro
        let assump_13 := assump_2 assump_147
        apply False.elim assump_13
      case inr assump_9 =>
        cases assump_9
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            have assump_148 : (((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) := by
              intro assump_46
              intro assump_47
              cases assump_46
              case inl assump_50 =>
                cases assump_50
                case inl assump_52 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_53 =>
                  apply Or.inr
                  apply True.intro
              case inr assump_51 =>
                cases assump_51
                case inl assump_58 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_59 =>
                  apply Or.inr
                  apply True.intro
            let assump_45 := assump_2 assump_148
            apply False.elim assump_45
          case inr assump_38 =>
            have assump_149 : (((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) := by
              intro assump_74
              intro assump_75
              cases assump_74
              case inl assump_78 =>
                cases assump_78
                case inl assump_80 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_81 =>
                  apply Or.inr
                  apply True.intro
              case inr assump_79 =>
                cases assump_79
                case inl assump_86 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_87 =>
                  apply Or.inr
                  apply True.intro
            let assump_73 := assump_2 assump_149
            apply False.elim assump_73
    case inr assump_7 =>
      cases assump_7
      case inl assump_95 =>
        have assump_150 : (((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) := by
          intro assump_101
          intro assump_102
          cases assump_101
          case inl assump_105 =>
            cases assump_105
            case inl assump_107 =>
              apply Or.inr
              apply True.intro
            case inr assump_108 =>
              apply Or.inr
              apply True.intro
          case inr assump_106 =>
            cases assump_106
            case inl assump_113 =>
              apply Or.inr
              apply True.intro
            case inr assump_114 =>
              apply Or.inr
              apply True.intro
        let assump_100 := assump_2 assump_150
        apply False.elim assump_100
      case inr assump_96 =>
        have assump_151 : (((p4 ∨ p0) ∨ (p6 ∨ p3)) → ((p7 → False) → (False ∨ True))) := by
          intro assump_126
          intro assump_127
          cases assump_126
          case inl assump_130 =>
            cases assump_130
            case inl assump_132 =>
              apply Or.inr
              apply True.intro
            case inr assump_133 =>
              apply Or.inr
              apply True.intro
          case inr assump_131 =>
            cases assump_131
            case inl assump_138 =>
              apply Or.inr
              apply True.intro
            case inr assump_139 =>
              apply Or.inr
              apply True.intro
        let assump_125 := assump_2 assump_151
        apply False.elim assump_125


variable (p5 p6 p3 p2 p7 : Prop)
theorem file74_25037 : ((((((p6 ∧ False) ∧ (p5 → False)) → False) ∨ (((False → p7) ∨ (p3 → False)) ∨ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p6 ∧ False) ∧ (p5 → False)) → False) ∨ (((False → p7) ∨ (p3 → False)) ∨ ((p2 → False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p5 p3 p6 p1 p4 p2 : Prop)
theorem file74_25619 : ((((((p6 ∨ p2) ∧ (p5 ∧ p4)) → ((p2 ∧ p1) → False)) ∧ (((p3 → p4) ∧ (False ∨ p2)) ∨ ((p4 ∧ p1) → False))) ∧ ((((False ∧ p0) ∧ (False → p5)) → ((False → False) → (p5 ∨ p2))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          cases assump_24
          case inl assump_27 =>
            apply False.elim assump_27
          case inr assump_28 =>
            have assump_67 : (((False ∧ p0) ∧ (False → p5)) → ((False → False) → (p5 ∨ p2))) := by
              intro assump_36
              intro assump_37
              cases assump_36
              case intro assump_40 assump_41 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42
            let assump_35 := assump_16 assump_67
            apply False.elim assump_35
      case inr assump_22 =>
        have assump_68 : (((False ∧ p0) ∧ (False → p5)) → ((False → False) → (p5 ∨ p2))) := by
          intro assump_54
          intro assump_55
          cases assump_54
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              apply False.elim assump_60
        let assump_53 := assump_16 assump_68
        apply False.elim assump_53


variable (p0 p1 p2 p6 p3 p4 p7 : Prop)
theorem file74_27146 : (((((p3 ∨ p7) ∧ (p7 ∧ p4)) → False) ∧ (((False → False) ∨ (p2 → False)) ∨ ((p2 → p2) ∨ (p6 → False)))) → ((((False ∧ p0) → False) ∨ ((p3 → p0) ∨ (p2 → False))) ∨ (((p4 ∨ p0) ∧ (p2 ∨ p4)) → ((p3 ∨ p4) ∧ (p1 ∨ p1))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
    case inr assump_7 =>
      cases assump_7
      case inl assump_24 =>
        apply Or.inl
        apply Or.inl
        intro assump_28
        cases assump_28
        case intro assump_29 assump_30 =>
          apply False.elim assump_29
      case inr assump_25 =>
        apply Or.inl
        apply Or.inl
        intro assump_35
        cases assump_35
        case intro assump_36 assump_37 =>
          apply False.elim assump_36


variable (p4 p6 p1 p0 p5 p7 p3 : Prop)
theorem file74_28396 : (((((p3 ∨ p1) ∨ (p7 → False)) ∨ ((p5 ∧ True) ∧ (False → False))) → (((False → False) ∨ (p7 ∨ p4)) ∨ ((p4 ∨ p4) ∨ (p4 → p6)))) ∨ ((((p6 → False) ∨ (p4 → p6)) → ((False → p5) → (p1 → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        apply Or.inl
        intro assump_10
        apply False.elim assump_10
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        intro assump_15
        apply False.elim assump_15
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
  case inr assump_3 =>
    cases assump_3
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply Or.inl
        apply Or.inl
        intro assump_33
        apply False.elim assump_33


variable (p3 p7 p4 p6 p0 p2 p5 : Prop)
theorem file74_29416 : ((((((p5 ∧ True) → (p5 ∧ True)) ∨ ((p2 → False) → False)) ∨ (((p4 ∨ p0) ∨ (p3 → False)) → ((p7 ∨ p6) ∨ (p5 ∨ False)))) → False) → False) := by
  intro assump_5
  have assump_19 : ((((p5 ∧ True) → (p5 ∧ True)) ∨ ((p2 → False) → False)) ∨ (((p4 ∨ p0) ∨ (p3 → False)) → ((p7 ∨ p6) ∨ (p5 ∨ False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      exact assump_10
    apply True.intro
  let assump_8 := assump_5 assump_19
  apply False.elim assump_8


variable (p7 p6 p2 : Prop)
theorem file74_30007 : ((((((p7 ∧ False) → False) → False) → (((True → p2) → (p6 → False)) ∨ ((p7 → False) ∧ (False → True)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p7 ∧ False) → False) → False) → (((True → p2) → (p6 → False)) ∨ ((p7 → False) ∧ (False → True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_32 : ((p7 ∧ False) → False) := by
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        apply False.elim assump_20
    let assump_17 := assump_5 assump_32
    apply False.elim assump_17
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p6 p5 p0 p1 p3 : Prop)
theorem file74_30715 : ((((((p6 ∧ p3) ∧ (p5 → True)) ∨ ((p0 → False) ∨ (False ∨ p6))) → (((False → p3) → False) → ((p5 ∧ p1) ∨ (p1 ∧ p0)))) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_30 : (((False → False) → False) → False) := by
      intro assump_17
      have assump_31 : (False → False) := by
        intro assump_21
        apply False.elim assump_21
      let assump_20 := assump_17 assump_31
      apply False.elim assump_20
    let assump_16 := assump_11 assump_30
    apply False.elim assump_16


variable (p5 p2 p7 : Prop)
theorem file74_31354 : (((((p5 ∧ False) ∧ (p7 → p2)) → ((True → False) → False)) → False) → ((((p2 ∨ p2) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_23 : (((p5 ∧ False) ∧ (p7 → p2)) → ((True → False) → False)) := by
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
  let assump_7 := assump_1 assump_23
  apply False.elim assump_7


variable (p2 p5 p6 p3 p1 : Prop)
theorem file74_31899 : (((((p1 ∧ p1) → (p5 ∧ p2)) ∨ ((p3 ∧ p5) → False)) ∧ (((p6 ∨ True) ∨ (p3 → False)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      have assump_26 : ((p6 ∨ True) ∨ (p3 → False)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_14 := assump_7 assump_26
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_27 : ((p6 ∨ True) ∨ (p3 → False)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_22 := assump_7 assump_27
      apply False.elim assump_22


variable (p2 p6 p7 p4 p0 p5 p1 p3 : Prop)
theorem file74_32609 : ((((((p7 → p6) → (False → False)) ∨ ((p3 → False) ∨ (p3 → p6))) → (((True → False) ∨ (p2 ∧ p4)) → False)) ∧ ((((p3 → False) ∨ (p3 → False)) ∧ ((p1 ∨ True) → False)) ∧ (((p0 → False) ∧ (p1 ∨ p5)) ∧ ((p7 ∨ p1) ∧ (p5 → False))))) → False) := by
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
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_17
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case inl assump_28 =>
                    have assump_140 : (p1 ∨ True) := by
                      apply Or.inl
                      exact assump_22
                    let assump_38 := assump_9 assump_140
                    apply False.elim assump_38
                  case inr assump_29 =>
                    have assump_141 : (p1 ∨ True) := by
                      apply Or.inl
                      exact assump_29
                    let assump_50 := assump_9 assump_141
                    apply False.elim assump_50
              case inr assump_23 =>
                cases assump_17
                case intro assump_56 assump_57 =>
                  cases assump_56
                  case inl assump_58 =>
                    have assump_142 : p5 := by
                      exact assump_23
                    let assump_64 := assump_57 assump_142
                    apply False.elim assump_64
                  case inr assump_59 =>
                    have assump_143 : p5 := by
                      exact assump_23
                    let assump_72 := assump_57 assump_143
                    apply False.elim assump_72
        case inr assump_11 =>
          cases assump_7
          case intro assump_80 assump_81 =>
            cases assump_80
            case intro assump_82 assump_83 =>
              cases assump_83
              case inl assump_86 =>
                cases assump_81
                case intro assump_90 assump_91 =>
                  cases assump_90
                  case inl assump_92 =>
                    have assump_144 : (p1 ∨ True) := by
                      apply Or.inl
                      exact assump_86
                    let assump_102 := assump_9 assump_144
                    apply False.elim assump_102
                  case inr assump_93 =>
                    have assump_145 : (p1 ∨ True) := by
                      apply Or.inl
                      exact assump_93
                    let assump_114 := assump_9 assump_145
                    apply False.elim assump_114
              case inr assump_87 =>
                cases assump_81
                case intro assump_120 assump_121 =>
                  cases assump_120
                  case inl assump_122 =>
                    have assump_146 : p5 := by
                      exact assump_87
                    let assump_128 := assump_121 assump_146
                    apply False.elim assump_128
                  case inr assump_123 =>
                    have assump_147 : p5 := by
                      exact assump_87
                    let assump_136 := assump_121 assump_147
                    apply False.elim assump_136


variable (p4 p7 p5 p2 p6 p1 p0 p3 : Prop)
theorem file74_36163 : (((((False → False) ∨ (p5 ∨ p1)) ∨ ((False ∨ p1) ∨ (p7 → False))) → (((p0 ∨ False) ∨ (False → p6)) ∧ ((p3 → p3) ∨ (p4 → False)))) ∨ ((((False ∧ p5) → (p3 → False)) → ((True → False) ∨ (True → False))) ∧ (((p5 → p2) ∨ (True ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_8
      apply False.elim assump_8
    case inr assump_5 =>
      cases assump_5
      case inl assump_11 =>
        apply Or.inr
        intro assump_15
        apply False.elim assump_15
      case inr assump_12 =>
        apply Or.inr
        intro assump_20
        apply False.elim assump_20
  case inr assump_3 =>
    cases assump_3
    case inl assump_23 =>
      cases assump_23
      case inl assump_25 =>
        apply False.elim assump_25
      case inr assump_26 =>
        apply Or.inr
        intro assump_31
        apply False.elim assump_31
    case inr assump_24 =>
      apply Or.inr
      intro assump_36
      apply False.elim assump_36
  cases assump_1
  case inl assump_39 =>
    cases assump_39
    case inl assump_41 =>
      apply Or.inl
      intro assump_45
      exact assump_45
    case inr assump_42 =>
      cases assump_42
      case inl assump_48 =>
        apply Or.inl
        intro assump_52
        exact assump_52
      case inr assump_49 =>
        apply Or.inl
        intro assump_57
        exact assump_57
  case inr assump_40 =>
    cases assump_40
    case inl assump_60 =>
      cases assump_60
      case inl assump_62 =>
        apply False.elim assump_62
      case inr assump_63 =>
        apply Or.inl
        intro assump_68
        exact assump_68
    case inr assump_61 =>
      apply Or.inl
      intro assump_73
      exact assump_73


variable (p2 p5 p6 p0 p4 p1 : Prop)
theorem file74_38032 : (((((p4 ∨ True) ∧ (p1 → False)) ∧ ((p6 → p5) ∧ (False ∧ p2))) ∧ (((p6 → p0) → False) ∧ ((p2 → p5) → (p2 → False)))) → ((((p0 ∧ p5) → (p1 → False)) → False) → (((p4 ∧ p4) → (True ∨ p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
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
              apply False.elim assump_24
        case inr assump_15 =>
          cases assump_11
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              apply False.elim assump_36


variable (p0 p7 p6 p5 p2 p4 : Prop)
theorem file74_38969 : (((((False ∨ False) ∧ (False → p7)) ∧ ((True → False) → (p4 ∧ p2))) ∧ (((p7 → False) ∨ (p6 ∨ p5)) ∨ ((p5 ∧ p5) → False))) → ((((False ∧ p2) ∨ (p0 → False)) → False) ∨ (((False → p7) → (p2 ∨ True)) ∧ ((p2 ∧ p0) ∨ (p0 → False))))) := by
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
          apply False.elim assump_9


variable (p5 p1 p7 p3 : Prop)
theorem file74_39593 : ((((((p1 ∨ True) → (p1 → p7)) → False) → (((p3 ∧ p3) → (p7 ∨ p3)) ∧ ((p7 ∨ p5) → (p5 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 ∨ True) → (p1 → p7)) → False) → (((p3 ∧ p3) → (p7 ∨ p3)) ∧ ((p7 ∨ p5) → (p5 ∨ p7)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inr
      exact assump_8
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply Or.inr
      exact assump_16
    case inr assump_17 =>
      apply Or.inl
      exact assump_17
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p4 p1 p5 p7 : Prop)
theorem file74_40291 : (((((p5 → False) ∧ (False ∧ p7)) → ((p7 ∧ p1) ∧ (p5 → p4))) → False) → False) := by
  intro assump_1
  have assump_36 : (((p5 → False) ∧ (False ∧ p7)) → ((p7 ∧ p1) ∧ (p5 → p4))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    intro assump_22
    cases assump_5
    case intro assump_25 assump_26 =>
      cases assump_26
      case intro assump_29 assump_30 =>
        apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p2 p5 p4 p3 p1 p0 : Prop)
theorem file74_41138 : (((((p1 ∧ p4) → (True ∨ True)) ∧ ((p0 ∨ True) → (True → p1))) → (((p5 ∧ True) ∨ (p2 → p2)) → ((True → False) → False))) ∨ ((((True ∧ True) → False) → ((False ∧ p0) → (True → p3))) ∨ (((p2 ∧ p4) → (False → p0)) → ((p4 → False) ∨ (True ∨ p1))))) := by
  apply Or.inl
  intro assump_8
  intro assump_9
  intro assump_10
  cases assump_9
  case inl assump_13 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        have assump_53 : True := by
          apply True.intro
        let assump_32 := assump_10 assump_53
        apply False.elim assump_32
  case inr assump_14 =>
    cases assump_8
    case intro assump_38 assump_39 =>
      have assump_54 : True := by
        apply True.intro
      let assump_49 := assump_10 assump_54
      apply False.elim assump_49


variable (p2 p1 p0 p4 p6 p7 p3 : Prop)
theorem file74_42037 : (((((p2 → False) → False) → ((p4 → False) → (p2 → p1))) → False) → ((((p2 ∨ p1) ∧ (False → False)) → ((p7 → False) ∧ (False → False))) → (((p6 → p7) → (p6 ∨ True)) ∨ ((p7 → p3) ∧ (False ∨ p0))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply Or.inr
  apply True.intro


variable (p2 : Prop)
theorem file74_42384 : ((((((False ∧ p2) → False) → False) → False) → False) → False) := by
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


variable (p2 p7 p0 p6 p5 : Prop)
theorem file74_42915 : ((((((True → False) → (True ∧ p2)) → False) → (((p7 → p6) → (p0 ∧ False)) ∨ ((p6 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((True → False) → (True ∧ p2)) → False) → (((p7 → p6) → (p0 ∧ False)) ∨ ((p6 → p5) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    have assump_41 : ((True → False) → (True ∧ p2)) := by
      intro assump_13
      apply And.intro
      apply True.intro
      have assump_42 : True := by
        apply True.intro
      let assump_16 := assump_13 assump_42
      apply False.elim assump_16
    let assump_12 := assump_5 assump_41
    apply False.elim assump_12
    have assump_43 : ((True → False) → (True ∧ p2)) := by
      intro assump_27
      apply And.intro
      apply True.intro
      have assump_44 : True := by
        apply True.intro
      let assump_30 := assump_27 assump_44
      apply False.elim assump_30
    let assump_26 := assump_5 assump_43
    apply False.elim assump_26
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p0 p1 p4 p5 p7 p2 p6 : Prop)
theorem file74_44040 : (((((p2 → False) ∧ (p7 → False)) → False) → False) → ((((p1 ∨ p0) ∧ (p5 → False)) → False) → (((p7 → False) ∨ (p6 → False)) ∨ ((p6 ∨ p1) ∧ (True ∧ p4))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  have assump_26 : (((p2 → False) ∧ (p7 → False)) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      have assump_27 : p7 := by
        exact assump_7
      let assump_19 := assump_14 assump_27
      apply False.elim assump_19
  let assump_11 := assump_1 assump_26
  apply False.elim assump_11


variable (p5 p4 p0 p7 p2 : Prop)
theorem file74_44680 : ((((((p2 ∨ p7) ∨ (p5 ∧ p0)) ∧ ((p4 → True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p2 ∨ p7) ∨ (p5 ∧ p0)) ∧ ((p4 → True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_47 : (p4 → True) := by
            intro assump_17
            apply True.intro
          let assump_16 := assump_7 assump_47
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_48 : (p4 → True) := by
            intro assump_26
            apply True.intro
          let assump_25 := assump_7 assump_48
          apply False.elim assump_25
      case inr assump_9 =>
        cases assump_9
        case intro assump_30 assump_31 =>
          have assump_49 : (p4 → True) := by
            intro assump_39
            apply True.intro
          let assump_38 := assump_7 assump_49
          apply False.elim assump_38
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p5 p7 p0 p1 p2 : Prop)
theorem file74_45842 : (((((p5 → p7) ∨ (p1 → False)) → ((p7 ∧ p1) ∨ (False → False))) → False) → ((((True ∧ p7) ∧ (p1 → p1)) ∧ ((p7 ∨ p5) → (True ∨ p2))) → (((True → False) ∧ (p1 → p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          have assump_43 : (((p5 → p7) ∨ (p1 → False)) → ((p7 ∧ p1) ∨ (False → False))) := by
            intro assump_27
            cases assump_27
            case inl assump_28 =>
              apply Or.inr
              intro assump_32
              apply False.elim assump_32
            case inr assump_29 =>
              apply Or.inr
              intro assump_37
              apply False.elim assump_37
          let assump_26 := assump_1 assump_43
          apply False.elim assump_26


variable (p6 p1 p4 p2 : Prop)
theorem file74_46860 : (((((p6 ∧ p4) ∨ (True ∧ True)) → False) → False) ∨ ((((False ∧ p2) → False) ∧ ((p6 → p4) → (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_36
  have assump_43 : ((p6 ∧ p4) ∨ (True ∧ True)) := by
    apply Or.inr
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_39 := assump_36 assump_43
  apply False.elim assump_39


variable (p3 p1 p0 p6 p4 p5 p2 : Prop)
theorem file74_47278 : (((((p4 ∨ p4) ∨ (p3 → False)) ∨ ((p6 ∧ p6) → (p5 → p2))) → (((False ∨ False) → (p2 ∨ p4)) ∨ ((p4 ∧ p5) → False))) ∨ ((((True → False) → (True → False)) → False) ∨ (((p4 → p1) → (False → p2)) → ((p6 → False) → (p0 ∧ p0))))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          apply False.elim assump_16
      case inr assump_11 =>
        apply Or.inl
        intro assump_23
        cases assump_23
        case inl assump_24 =>
          apply False.elim assump_24
        case inr assump_25 =>
          apply False.elim assump_25
    case inr assump_9 =>
      apply Or.inl
      intro assump_32
      cases assump_32
      case inl assump_33 =>
        apply False.elim assump_33
      case inr assump_34 =>
        apply False.elim assump_34
  case inr assump_7 =>
    apply Or.inl
    intro assump_41
    cases assump_41
    case inl assump_42 =>
      apply False.elim assump_42
    case inr assump_43 =>
      apply False.elim assump_43


variable (p3 p0 p2 p1 p7 p5 p4 : Prop)
theorem file74_48581 : (((((p0 → False) → False) ∧ ((False ∧ p5) → (p4 ∨ p4))) → (((p5 ∧ p3) ∨ (p2 → p1)) → ((p7 ∧ p3) ∨ (p1 ∨ False)))) → ((((p5 → False) ∧ (False ∨ p5)) → False) ∨ (((p2 → False) ∨ (p4 ∧ p0)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      have assump_20 : p5 := by
        exact assump_10
      let assump_16 := assump_5 assump_20
      apply False.elim assump_16


variable (p1 p6 p3 p2 p7 p5 : Prop)
theorem file74_49178 : ((((((False ∧ p6) → False) ∨ ((True → False) ∨ (p1 ∧ p5))) ∨ (((p7 → p3) → (p5 → p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p6) → False) ∨ ((True → False) ∨ (p1 ∧ p5))) ∨ (((p7 → p3) → (p5 → p2)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p4 p0 p3 p1 p2 p7 p5 : Prop)
theorem file74_49705 : ((((((p7 → False) → (p0 → False)) ∧ ((p5 ∧ p3) → (p3 → False))) ∧ (((p1 → True) → (True ∧ p5)) → ((p6 → p6) → (p4 ∨ False)))) ∧ ((((False → False) ∨ (True ∧ p4)) ∨ ((p2 ∨ False) ∨ (p0 → p6))) ∧ (((True ∧ p1) ∨ (False → True)) → ((False ∧ p6) ∧ (p4 → p0))))) → False) := by
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
            cases assump_16
            case inl assump_18 =>
              have assump_74 : ((True ∧ p1) ∨ (False → True)) := by
                apply Or.inr
                intro assump_25
                apply True.intro
              let assump_24 := assump_15 assump_74
              let assump_26 := And.left assump_24
              let assump_27 := And.left assump_26
              apply False.elim assump_27
            case inr assump_19 =>
              cases assump_19
              case intro assump_31 assump_32 =>
                have assump_75 : ((True ∧ p1) ∨ (False → True)) := by
                  apply Or.inr
                  intro assump_40
                  apply True.intro
                let assump_39 := assump_15 assump_75
                let assump_41 := And.left assump_39
                let assump_42 := And.left assump_41
                apply False.elim assump_42
          case inr assump_17 =>
            cases assump_17
            case inl assump_46 =>
              cases assump_46
              case inl assump_48 =>
                have assump_76 : ((True ∧ p1) ∨ (False → True)) := by
                  apply Or.inr
                  intro assump_55
                  apply True.intro
                let assump_54 := assump_15 assump_76
                let assump_56 := And.left assump_54
                let assump_57 := And.left assump_56
                apply False.elim assump_57
              case inr assump_49 =>
                apply False.elim assump_49
            case inr assump_47 =>
              have assump_77 : ((True ∧ p1) ∨ (False → True)) := by
                apply Or.inr
                intro assump_68
                apply True.intro
              let assump_67 := assump_15 assump_77
              let assump_69 := And.left assump_67
              let assump_70 := And.left assump_69
              apply False.elim assump_70


variable (p6 p2 p3 p7 p0 : Prop)
theorem file74_52235 : ((((((True ∨ p7) ∨ (False ∧ p3)) ∧ ((False → p7) ∧ (p7 → True))) ∧ (((p6 ∨ False) ∧ (p2 → False)) ∨ ((False ∧ p0) ∨ (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((True ∨ p7) ∨ (False ∧ p3)) ∧ ((False → p7) ∧ (p7 → True))) ∧ (((p6 ∨ False) ∧ (p2 → False)) ∨ ((False ∧ p0) ∨ (True ∨ True)))) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    apply Or.inl
    apply True.intro
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply True.intro
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p7 p3 p2 p6 p5 p0 : Prop)
theorem file74_52969 : ((((((p6 ∧ p5) ∧ (p4 ∨ p4)) ∧ ((p0 → p4) → (p7 → False))) ∧ (((p4 → False) → (p7 → False)) ∨ ((False ∧ p6) → False))) ∧ ((((p7 ∨ p0) ∨ (p3 → p6)) ∨ ((p5 ∧ p2) → False)) → (((p4 ∧ p5) ∨ (p4 ∨ p6)) → ((p7 → p6) ∧ (p6 → False))))) → False) := by
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
            cases assump_9
            case inl assump_16 =>
              cases assump_5
              case inl assump_22 =>
                have assump_90 : (((p7 ∨ p0) ∨ (p3 → p6)) ∨ ((p5 ∧ p2) → False)) := by
                  apply Or.inl
                  apply Or.inr
                  intro assump_29
                  exact assump_10
                let assump_28 := assump_3 assump_90
                have assump_91 : ((p4 ∧ p5) ∨ (p4 ∨ p6)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_16
                  exact assump_11
                let assump_32 := assump_28 assump_91
                let assump_33 := And.right assump_32
                have assump_92 : p6 := by
                  exact assump_10
                let assump_35 := assump_33 assump_92
                apply False.elim assump_35
              case inr assump_23 =>
                have assump_93 : (((p7 ∨ p0) ∨ (p3 → p6)) ∨ ((p5 ∧ p2) → False)) := by
                  apply Or.inl
                  apply Or.inr
                  intro assump_44
                  exact assump_10
                let assump_43 := assump_3 assump_93
                have assump_94 : ((p4 ∧ p5) ∨ (p4 ∨ p6)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_16
                  exact assump_11
                let assump_47 := assump_43 assump_94
                let assump_48 := And.right assump_47
                have assump_95 : p6 := by
                  exact assump_10
                let assump_50 := assump_48 assump_95
                apply False.elim assump_50
            case inr assump_17 =>
              cases assump_5
              case inl assump_58 =>
                have assump_96 : (((p7 ∨ p0) ∨ (p3 → p6)) ∨ ((p5 ∧ p2) → False)) := by
                  apply Or.inl
                  apply Or.inr
                  intro assump_65
                  exact assump_10
                let assump_64 := assump_3 assump_96
                have assump_97 : ((p4 ∧ p5) ∨ (p4 ∨ p6)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_17
                  exact assump_11
                let assump_68 := assump_64 assump_97
                let assump_69 := And.right assump_68
                have assump_98 : p6 := by
                  exact assump_10
                let assump_71 := assump_69 assump_98
                apply False.elim assump_71
              case inr assump_59 =>
                have assump_99 : (((p7 ∨ p0) ∨ (p3 → p6)) ∨ ((p5 ∧ p2) → False)) := by
                  apply Or.inl
                  apply Or.inr
                  intro assump_80
                  exact assump_10
                let assump_79 := assump_3 assump_99
                have assump_100 : ((p4 ∧ p5) ∨ (p4 ∨ p6)) := by
                  apply Or.inl
                  apply And.intro
                  exact assump_17
                  exact assump_11
                let assump_83 := assump_79 assump_100
                let assump_84 := And.right assump_83
                have assump_101 : p6 := by
                  exact assump_10
                let assump_86 := assump_84 assump_101
                apply False.elim assump_86


variable (p4 : Prop)
theorem file74_56844 : (((((True ∧ True) ∧ (False → p4)) ∧ ((p4 → False) → (False → False))) → False) → False) := by
  intro assump_19
  have assump_33 : (((True ∧ True) ∧ (False → p4)) ∧ ((p4 → False) → (False → False))) := by
    apply And.intro
    apply And.intro
    apply And.intro
    apply True.intro
    apply True.intro
    intro assump_23
    apply False.elim assump_23
    intro assump_26
    intro assump_27
    apply False.elim assump_27
  let assump_22 := assump_19 assump_33
  apply False.elim assump_22


variable (p5 p6 p7 p4 p2 : Prop)
theorem file74_57398 : (((((p7 → False) ∧ (p5 ∧ p2)) ∧ ((True ∧ p4) → False)) ∧ (((p5 ∨ False) → False) ∧ ((p4 → False) ∨ (True ∨ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              have assump_46 : (p5 ∨ False) := by
                apply Or.inl
                exact assump_10
              let assump_27 := assump_18 assump_46
              apply False.elim assump_27
            case inr assump_23 =>
              cases assump_23
              case inl assump_31 =>
                have assump_47 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_10
                let assump_35 := assump_18 assump_47
                apply False.elim assump_35
              case inr assump_32 =>
                have assump_48 : (p5 ∨ False) := by
                  apply Or.inl
                  exact assump_10
                let assump_42 := assump_18 assump_48
                apply False.elim assump_42


variable (p0 p7 p1 p4 p6 p5 p3 : Prop)
theorem file74_58733 : (((((p7 → False) ∧ (False ∨ False)) ∧ ((True → p3) → False)) → False) ∨ ((((p5 → False) → (p5 → False)) → ((p3 ∧ p6) ∨ (p1 ∧ p3))) → (((p0 ∨ p4) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        apply False.elim assump_9


variable (p4 p6 p5 p7 : Prop)
theorem file74_59239 : ((((((False → p4) ∨ (p6 ∨ p4)) → ((p6 ∨ p7) → False)) → (((p4 → p5) ∧ (p5 ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → p4) ∨ (p6 ∨ p4)) → ((p6 ∨ p7) → False)) → (((p4 → p5) ∧ (p5 ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p6 p5 p7 p2 p1 p3 p4 p0 : Prop)
theorem file74_59811 : (((((p3 ∧ True) ∧ (p5 → False)) ∧ ((p0 → False) ∨ (p0 ∨ p1))) ∧ (((p0 → p3) → False) ∧ ((p5 ∧ p5) ∨ (p2 → p7)))) → ((((p0 ∨ p6) ∧ (p5 → p5)) ∨ ((p3 → p4) ∧ (True → False))) ∨ (((p2 ∧ p0) ∨ (p2 ∧ False)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case inl assump_16 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply Or.inl
                  apply Or.inr
                  apply And.intro
                  intro assump_32
                  have assump_170 : (p0 → p3) := by
                    intro assump_39
                    exact assump_32
                  let assump_38 := assump_20 assump_170
                  apply False.elim assump_38
                  intro assump_45
                  have assump_171 : (p0 → p3) := by
                    intro assump_51
                    exact assump_8
                  let assump_50 := assump_20 assump_171
                  apply False.elim assump_50
              case inr assump_25 =>
                apply Or.inl
                apply Or.inr
                apply And.intro
                intro assump_59
                have assump_172 : (p0 → p3) := by
                  intro assump_65
                  exact assump_59
                let assump_64 := assump_20 assump_172
                apply False.elim assump_64
                intro assump_71
                have assump_173 : (p0 → p3) := by
                  intro assump_76
                  exact assump_8
                let assump_75 := assump_20 assump_173
                apply False.elim assump_75
          case inr assump_17 =>
            cases assump_17
            case inl assump_82 =>
              cases assump_3
              case intro assump_86 assump_87 =>
                cases assump_87
                case inl assump_90 =>
                  cases assump_90
                  case intro assump_92 assump_93 =>
                    apply Or.inl
                    apply Or.inl
                    apply And.intro
                    apply Or.inl
                    exact assump_82
                    intro assump_98
                    exact assump_98
                case inr assump_91 =>
                  apply Or.inl
                  apply Or.inl
                  apply And.intro
                  apply Or.inl
                  exact assump_82
                  intro assump_103
                  exact assump_103
            case inr assump_83 =>
              cases assump_3
              case intro assump_108 assump_109 =>
                cases assump_109
                case inl assump_112 =>
                  cases assump_112
                  case intro assump_114 assump_115 =>
                    apply Or.inl
                    apply Or.inr
                    apply And.intro
                    intro assump_120
                    have assump_174 : (p0 → p3) := by
                      intro assump_127
                      exact assump_120
                    let assump_126 := assump_108 assump_174
                    apply False.elim assump_126
                    intro assump_133
                    have assump_175 : (p0 → p3) := by
                      intro assump_139
                      exact assump_8
                    let assump_138 := assump_108 assump_175
                    apply False.elim assump_138
                case inr assump_113 =>
                  apply Or.inl
                  apply Or.inr
                  apply And.intro
                  intro assump_147
                  have assump_176 : (p0 → p3) := by
                    intro assump_153
                    exact assump_147
                  let assump_152 := assump_108 assump_176
                  apply False.elim assump_152
                  intro assump_159
                  have assump_177 : (p0 → p3) := by
                    intro assump_164
                    exact assump_8
                  let assump_163 := assump_108 assump_177
                  apply False.elim assump_163


variable (p4 p5 p6 p3 : Prop)
theorem file74_64287 : (((((p5 → False) → False) ∧ ((True → False) ∨ (p5 → False))) → False) ∨ ((((p3 → True) → (True ∧ p5)) ∧ ((p6 ∨ p3) ∨ (p4 → False))) → (((False ∨ p3) ∧ (p3 ∧ False)) ∨ ((True → False) → False)))) := by
  apply Or.inl
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      have assump_36 : True := by
        apply True.intro
      let assump_17 := assump_13 assump_36
      apply False.elim assump_17
    case inr assump_14 =>
      have assump_37 : (p5 → False) := by
        intro assump_25
        have assump_38 : p5 := by
          exact assump_25
        let assump_29 := assump_14 assump_38
        apply False.elim assump_29
      let assump_24 := assump_9 assump_37
      apply False.elim assump_24


variable (p1 p7 p6 p0 p4 p2 p5 : Prop)
theorem file74_65123 : (((((p4 ∨ p5) ∧ (p6 ∨ p6)) ∧ ((p2 → False) ∧ (p0 ∨ p7))) ∧ (((p4 → p7) → (p2 ∨ p1)) → False)) → ((((True → False) ∧ (p4 ∧ False)) → ((False ∧ p5) → (p7 ∧ p4))) ∨ (((p1 → p7) → False) → False))) := by
  intro assump_27
  cases assump_27
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          cases assump_33
          case inl assump_38 =>
            cases assump_31
            case intro assump_42 assump_43 =>
              cases assump_43
              case inl assump_46 =>
                apply Or.inl
                intro assump_52
                intro assump_53
                apply And.intro
                cases assump_53
                case intro assump_54 assump_55 =>
                  apply False.elim assump_54
                cases assump_53
                case intro assump_58 assump_59 =>
                  apply False.elim assump_58
              case inr assump_47 =>
                apply Or.inl
                intro assump_66
                intro assump_67
                apply And.intro
                cases assump_67
                case intro assump_68 assump_69 =>
                  apply False.elim assump_68
                cases assump_67
                case intro assump_72 assump_73 =>
                  apply False.elim assump_72
          case inr assump_39 =>
            cases assump_31
            case intro assump_78 assump_79 =>
              cases assump_79
              case inl assump_82 =>
                apply Or.inl
                intro assump_88
                intro assump_89
                apply And.intro
                cases assump_89
                case intro assump_90 assump_91 =>
                  apply False.elim assump_90
                cases assump_89
                case intro assump_94 assump_95 =>
                  apply False.elim assump_94
              case inr assump_83 =>
                apply Or.inl
                intro assump_102
                intro assump_103
                apply And.intro
                cases assump_103
                case intro assump_104 assump_105 =>
                  apply False.elim assump_104
                cases assump_103
                case intro assump_108 assump_109 =>
                  apply False.elim assump_108
        case inr assump_35 =>
          cases assump_33
          case inl assump_114 =>
            cases assump_31
            case intro assump_118 assump_119 =>
              cases assump_119
              case inl assump_122 =>
                apply Or.inl
                intro assump_128
                intro assump_129
                apply And.intro
                cases assump_129
                case intro assump_130 assump_131 =>
                  apply False.elim assump_130
                cases assump_129
                case intro assump_134 assump_135 =>
                  apply False.elim assump_134
              case inr assump_123 =>
                apply Or.inl
                intro assump_142
                intro assump_143
                apply And.intro
                cases assump_143
                case intro assump_144 assump_145 =>
                  apply False.elim assump_144
                cases assump_143
                case intro assump_148 assump_149 =>
                  apply False.elim assump_148
          case inr assump_115 =>
            cases assump_31
            case intro assump_154 assump_155 =>
              cases assump_155
              case inl assump_158 =>
                apply Or.inl
                intro assump_164
                intro assump_165
                apply And.intro
                cases assump_165
                case intro assump_166 assump_167 =>
                  apply False.elim assump_166
                cases assump_165
                case intro assump_170 assump_171 =>
                  apply False.elim assump_170
              case inr assump_159 =>
                apply Or.inl
                intro assump_178
                intro assump_179
                apply And.intro
                cases assump_179
                case intro assump_180 assump_181 =>
                  apply False.elim assump_180
                cases assump_179
                case intro assump_184 assump_185 =>
                  apply False.elim assump_184


variable (p4 p5 p0 p1 p2 p3 p6 p7 : Prop)
theorem file74_69643 : (((((p1 ∧ p3) → (p2 ∧ True)) ∧ ((False ∧ p4) → False)) ∧ (((True ∧ p6) → False) ∧ ((p3 → p3) → False))) → ((((p7 → p1) → False) → ((p0 → p4) → (False → p5))) → (((p4 ∨ False) ∨ (p5 ∨ p5)) → False))) := by
  intro assump_27
  intro assump_28
  intro assump_29
  cases assump_29
  case inl assump_30 =>
    cases assump_30
    case inl assump_32 =>
      cases assump_27
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_39
          case intro assump_46 assump_47 =>
            have assump_113 : (p3 → p3) := by
              intro assump_53
              exact assump_53
            let assump_52 := assump_47 assump_113
            apply False.elim assump_52
    case inr assump_33 =>
      apply False.elim assump_33
  case inr assump_31 =>
    cases assump_31
    case inl assump_61 =>
      cases assump_27
      case intro assump_67 assump_68 =>
        cases assump_67
        case intro assump_69 assump_70 =>
          cases assump_68
          case intro assump_75 assump_76 =>
            have assump_114 : (p3 → p3) := by
              intro assump_82
              exact assump_82
            let assump_81 := assump_76 assump_114
            apply False.elim assump_81
    case inr assump_62 =>
      cases assump_27
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_93
          case intro assump_100 assump_101 =>
            have assump_115 : (p3 → p3) := by
              intro assump_107
              exact assump_107
            let assump_106 := assump_101 assump_115
            apply False.elim assump_106


variable (p1 : Prop)
theorem file74_71376 : ((((((p1 → False) → (True ∨ False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → False) → (True ∨ False)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p1 → False) → (True ∨ False)) := by
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p2 p1 p5 p7 p0 p3 p6 : Prop)
theorem file74_71889 : ((((((p1 → p3) ∧ (p0 → False)) ∨ ((p7 ∨ p1) ∨ (p2 ∨ p4))) → (((False → p7) ∨ (p7 → p4)) ∨ ((p5 ∨ p1) ∧ (p6 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p1 → p3) ∧ (p0 → False)) ∨ ((p7 ∨ p1) ∨ (p2 ∨ p4))) → (((False → p7) ∨ (p7 → p4)) ∨ ((p5 ∨ p1) ∧ (p6 ∧ True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
    case inr assump_7 =>
      cases assump_7
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          apply Or.inl
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
        case inr assump_20 =>
          apply Or.inl
          apply Or.inl
          intro assump_28
          apply False.elim assump_28
      case inr assump_18 =>
        cases assump_18
        case inl assump_31 =>
          apply Or.inl
          apply Or.inl
          intro assump_35
          apply False.elim assump_35
        case inr assump_32 =>
          apply Or.inl
          apply Or.inl
          intro assump_40
          apply False.elim assump_40
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p3 p2 p1 p4 p7 p0 : Prop)
theorem file74_73243 : ((((((False → True) ∧ (False → False)) ∧ ((p3 ∧ False) → False)) ∨ (((False → p7) ∨ (p1 ∨ p4)) ∨ ((p2 → p0) ∨ (p1 → p4)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → True) ∧ (False → False)) ∧ ((p3 ∧ False) → False)) ∨ (((False → p7) ∨ (p1 ∨ p4)) ∨ ((p2 → p0) ∨ (p1 → p4)))) := by
    apply Or.inl
    apply And.intro
    apply And.intro
    intro assump_5
    apply True.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p0 p4 p6 : Prop)
theorem file74_73927 : ((((((p0 ∧ p6) ∧ (p1 ∧ False)) ∧ ((p1 → False) → (p4 ∧ True))) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p0 ∧ p6) ∧ (p1 ∧ False)) ∧ ((p1 → False) → (p4 ∧ True))) → False) := by
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


variable (p3 p5 p6 p1 p2 p4 p7 p0 : Prop)
theorem file74_74572 : (((((False ∨ p7) ∨ (p6 ∨ p7)) ∧ ((p5 ∨ p3) ∧ (True ∧ False))) → False) ∨ ((((p0 → p7) → False) ∧ ((p5 ∨ True) ∨ (p2 ∨ p5))) ∧ (((p1 ∨ p3) → False) ∨ ((False → False) ∧ (p7 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply False.elim assump_6
      case inr assump_7 =>
        cases assump_3
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
    case inr assump_5 =>
      cases assump_5
      case inl assump_32 =>
        cases assump_3
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            cases assump_37
            case intro assump_42 assump_43 =>
              apply False.elim assump_43
          case inr assump_39 =>
            cases assump_37
            case intro assump_50 assump_51 =>
              apply False.elim assump_51
      case inr assump_33 =>
        cases assump_3
        case intro assump_58 assump_59 =>
          cases assump_58
          case inl assump_60 =>
            cases assump_59
            case intro assump_64 assump_65 =>
              apply False.elim assump_65
          case inr assump_61 =>
            cases assump_59
            case intro assump_72 assump_73 =>
              apply False.elim assump_73


variable (p0 p6 p4 p2 : Prop)
theorem file74_76307 : (((((p4 ∧ p4) ∨ (p0 → p0)) → ((p2 → False) → (p6 → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p4 ∧ p4) ∨ (p0 → p0)) → ((p2 → False) → (p6 → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p7 p2 p0 p5 : Prop)
theorem file74_76689 : (((((True ∧ p5) ∧ (p0 → True)) → ((p2 → True) ∨ (p1 → p2))) ∨ (((p5 → False) ∧ (p1 ∨ True)) → ((p7 ∨ p5) → False))) ∨ ((((p1 ∨ p2) ∨ (p7 → p0)) ∧ ((p7 ∧ False) ∧ (p1 ∨ p5))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      apply True.intro


variable (p0 p2 p6 p3 p7 : Prop)
theorem file74_77153 : (((((False → False) ∨ (p0 ∧ p3)) ∧ ((True → False) → (p7 ∨ p0))) ∨ (((p3 → p7) ∧ (p0 ∨ p3)) ∨ ((p7 ∧ p2) → False))) ∨ ((((p6 → p3) ∧ (p6 → p6)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_5
  apply False.elim assump_5
  intro assump_8
  have assump_15 : True := by
    apply True.intro
  let assump_11 := assump_8 assump_15
  apply False.elim assump_11


variable (p7 p1 p0 p3 p4 p6 p5 : Prop)
theorem file74_77628 : (((((p6 → False) ∧ (p6 → False)) → ((p7 → False) → (p7 ∧ p5))) → False) → ((((p6 ∨ p7) ∧ (True ∧ p0)) ∨ ((p7 → False) ∨ (True → p3))) ∨ (((False ∧ p0) ∨ (p5 ∨ p5)) ∧ ((p1 ∧ p4) → (False → True))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_4
  have assump_36 : (((p6 → False) ∧ (p6 → False)) → ((p7 → False) → (p7 ∧ p5))) := by
    intro assump_9
    intro assump_10
    apply And.intro
    cases assump_9
    case intro assump_13 assump_14 =>
      exact assump_4
    cases assump_9
    case intro assump_21 assump_22 =>
      have assump_37 : p7 := by
        exact assump_4
      let assump_29 := assump_10 assump_37
      apply False.elim assump_29
  let assump_8 := assump_1 assump_36
  apply False.elim assump_8


variable (p4 p1 p3 p7 p2 p0 : Prop)
theorem file74_78447 : (((((False → p4) ∨ (p1 → False)) → False) → (((p2 ∨ p7) ∧ (p7 → p7)) ∨ ((p3 ∨ True) → False))) ∨ ((((False ∨ p2) → False) ∨ ((False ∧ p0) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_26 : ((False → p4) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_11
      apply False.elim assump_11
    let assump_10 := assump_1 assump_26
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_27 : ((False → p4) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_1 assump_27
    apply False.elim assump_19


variable (p7 p0 p5 p4 p6 : Prop)
theorem file74_79199 : (((((True → False) → (p6 ∨ p5)) → False) ∧ (((p5 ∨ True) ∨ (p0 ∧ False)) → ((False ∨ p5) → False))) → ((((p4 ∨ False) → (p0 → p7)) ∨ ((False → False) → False)) → False)) := by
  intro assump_7
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    cases assump_7
    case intro assump_13 assump_14 =>
      have assump_53 : ((True → False) → (p6 ∨ p5)) := by
        intro assump_22
        have assump_54 : True := by
          apply True.intro
        let assump_25 := assump_22 assump_54
        apply False.elim assump_25
      let assump_21 := assump_13 assump_53
      apply False.elim assump_21
  case inr assump_10 =>
    cases assump_7
    case intro assump_34 assump_35 =>
      have assump_55 : ((True → False) → (p6 ∨ p5)) := by
        intro assump_43
        have assump_56 : True := by
          apply True.intro
        let assump_46 := assump_43 assump_56
        apply False.elim assump_46
      let assump_42 := assump_34 assump_55
      apply False.elim assump_42


variable (p7 p5 : Prop)
theorem file74_80237 : ((((((False → p5) → (False → p7)) → False) → False) → False) → False) := by
  intro assump_5
  have assump_23 : ((((False → p5) → (False → p7)) → False) → False) := by
    intro assump_9
    have assump_24 : ((False → p5) → (False → p7)) := by
      intro assump_13
      intro assump_14
      apply False.elim assump_14
    let assump_12 := assump_9 assump_24
    apply False.elim assump_12
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p2 p1 p3 p0 p5 p4 p6 : Prop)
theorem file74_80757 : (((((False ∧ p0) ∧ (p3 → False)) ∧ ((p6 → True) → (p6 ∧ p5))) ∧ (((p5 → False) → False) → ((p4 ∨ p5) → (p4 ∧ p4)))) → ((((True ∧ p6) ∨ (True → p2)) → ((p3 → p6) ∧ (p6 ∨ False))) → (((p6 ∨ p5) → (p1 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_14


variable (p5 p7 p3 p0 p2 p4 : Prop)
theorem file74_81366 : ((((((p0 → False) → (False → p3)) ∨ ((p5 ∨ True) → (p2 → False))) ∨ (((p4 → False) → False) ∧ ((p7 ∧ p0) ∨ (p3 ∨ p7)))) → False) → False) := by
  intro assump_11
  have assump_22 : ((((p0 → False) → (False → p3)) ∨ ((p5 ∨ True) → (p2 → False))) ∨ (((p4 → False) → False) ∧ ((p7 ∧ p0) ∨ (p3 ∨ p7)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_15
    intro assump_16
    apply False.elim assump_16
  let assump_14 := assump_11 assump_22
  apply False.elim assump_14


variable (p4 p0 p7 p5 : Prop)
theorem file74_81898 : ((((((p5 ∨ p5) ∧ (p0 → p5)) → ((True → False) → (p4 → True))) ∨ (((p7 ∧ p0) ∨ (p4 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∨ p5) ∧ (p0 → p5)) → ((True → False) → (p4 → True))) ∨ (((p7 ∧ p0) ∨ (p4 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p3 p7 p4 p2 p0 p1 : Prop)
theorem file74_82389 : (((((p1 → p0) ∧ (p7 ∨ p1)) ∧ ((p4 → False) ∧ (False ∨ p4))) → (((True ∧ p0) ∨ (False → False)) ∨ ((True → True) → False))) ∨ ((((p4 ∧ p5) ∨ (p7 ∧ p7)) ∧ ((p3 ∨ p7) ∧ (p7 → p3))) → (((p2 ∨ p4) → (True → False)) → False))) := by
  apply Or.inl
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
          case inl assump_16 =>
            apply False.elim assump_16
          case inr assump_17 =>
            apply Or.inl
            apply Or.inr
            intro assump_22
            apply False.elim assump_22
      case inr assump_9 =>
        cases assump_3
        case intro assump_27 assump_28 =>
          cases assump_28
          case inl assump_31 =>
            apply False.elim assump_31
          case inr assump_32 =>
            apply Or.inl
            apply Or.inr
            intro assump_37
            apply False.elim assump_37


variable (p7 p1 p5 p4 p6 p3 : Prop)
theorem file74_83511 : ((((((True ∨ p4) → False) ∧ ((True → p6) ∧ (p7 → False))) → (((p4 ∧ p4) ∨ (p3 ∨ False)) ∧ ((p4 → False) ∧ (p1 ∧ p5)))) → False) → False) := by
  intro assump_27
  have assump_106 : ((((True ∨ p4) → False) ∧ ((True → p6) ∧ (p7 → False))) → (((p4 ∧ p4) ∨ (p3 ∨ False)) ∧ ((p4 → False) ∧ (p1 ∧ p5)))) := by
    intro assump_31
    apply And.intro
    cases assump_31
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        have assump_107 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_45 := assump_32 assump_107
        apply False.elim assump_45
    apply And.intro
    intro assump_49
    cases assump_31
    case intro assump_52 assump_53 =>
      cases assump_53
      case intro assump_56 assump_57 =>
        have assump_108 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_65 := assump_52 assump_108
        apply False.elim assump_65
    apply And.intro
    cases assump_31
    case intro assump_69 assump_70 =>
      cases assump_70
      case intro assump_73 assump_74 =>
        have assump_109 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_82 := assump_69 assump_109
        apply False.elim assump_82
    cases assump_31
    case intro assump_86 assump_87 =>
      cases assump_87
      case intro assump_90 assump_91 =>
        have assump_110 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_99 := assump_86 assump_110
        apply False.elim assump_99
  let assump_30 := assump_27 assump_106
  apply False.elim assump_30


variable (p3 p5 p1 p2 p4 p7 : Prop)
theorem file74_85224 : (((((p3 → p1) → (p5 ∨ True)) ∨ ((p3 → False) ∧ (False ∨ p5))) ∧ (((p1 ∨ p4) ∨ (True ∨ p2)) → ((False → p7) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_38 : ((p1 ∨ p4) ∨ (True ∨ p2)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_38
      have assump_39 : (False → p7) := by
        intro assump_12
        apply False.elim assump_12
      let assump_11 := assump_10 assump_39
      apply False.elim assump_11
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          apply False.elim assump_22
        case inr assump_23 =>
          have assump_40 : ((p1 ∨ p4) ∨ (True ∨ p2)) := by
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_30 := assump_3 assump_40
          have assump_41 : (False → p7) := by
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_30 assump_41
          apply False.elim assump_31


variable (p6 p2 p3 p5 p4 p1 p7 p0 : Prop)
theorem file74_86464 : (((((p3 → False) ∧ (p5 → False)) → ((p2 → True) ∨ (p1 → False))) ∨ (((p7 → False) ∧ (p4 ∧ p6)) ∧ ((p0 ∨ p5) → (True ∨ False)))) ∨ ((((p1 → False) → (p1 → False)) ∨ ((p3 ∨ p2) ∨ (p1 ∨ p0))) ∨ (((p3 ∨ True) → False) → ((True → p6) → (True → True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    apply Or.inl
    intro assump_29
    apply True.intro


variable (p3 p0 p4 p5 p7 p1 p2 : Prop)
theorem file74_86942 : (((((p1 ∧ p4) → (p7 → False)) → ((False ∧ p7) ∨ (p2 ∧ p0))) → False) → ((((p5 → True) ∨ (p3 ∧ p7)) ∨ ((p5 → False) → (p1 → False))) ∨ (((p1 → False) → (p4 ∧ p7)) ∧ ((p1 ∨ p3) → (True ∨ p4))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p6 p2 p4 p7 p5 p1 p3 : Prop)
theorem file74_87302 : ((((((False ∨ p6) ∧ (p7 ∧ p5)) → ((p1 → p4) → False)) → (((p4 ∧ p4) ∨ (p7 → False)) ∧ ((p5 → p2) → (p2 ∧ p2)))) ∧ ((((False ∨ p2) ∧ (p1 → False)) ∨ ((True → p2) → (p2 ∧ p3))) ∧ (((p5 → False) → (p3 → False)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              have assump_48 : (False → False) := by
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_21 assump_48
              apply False.elim assump_26
      case inr assump_9 =>
        cases assump_7
        case intro assump_35 assump_36 =>
          have assump_49 : (False → False) := by
            intro assump_42
            apply False.elim assump_42
          let assump_41 := assump_36 assump_49
          apply False.elim assump_41


variable (p1 p3 : Prop)
theorem file74_88554 : (((((False → False) ∨ (p1 → True)) ∨ ((False → False) ∨ (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p1 → True)) ∨ ((False → False) ∨ (p3 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p1 p7 p3 p0 p6 p5 p2 : Prop)
theorem file74_88974 : (((((p1 ∧ p6) ∨ (p2 → p5)) ∧ ((True → False) ∨ (True → False))) → (((p2 ∨ p0) ∨ (p4 ∧ False)) ∧ ((p1 → p6) → (False ∨ p3)))) ∨ ((((p3 → False) ∧ (p3 → p6)) → False) ∨ (((p0 → False) ∨ (p7 → p0)) → ((p3 ∧ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case inl assump_12 =>
          have assump_85 : True := by
            apply True.intro
          let assump_16 := assump_12 assump_85
          apply False.elim assump_16
        case inr assump_13 =>
          have assump_86 : True := by
            apply True.intro
          let assump_22 := assump_13 assump_86
          apply False.elim assump_22
    case inr assump_5 =>
      cases assump_3
      case inl assump_28 =>
        have assump_87 : True := by
          apply True.intro
        let assump_32 := assump_28 assump_87
        apply False.elim assump_32
      case inr assump_29 =>
        have assump_88 : True := by
          apply True.intro
        let assump_38 := assump_29 assump_88
        apply False.elim assump_38
  intro assump_42
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_45
    case inl assump_47 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        cases assump_46
        case inl assump_55 =>
          have assump_89 : True := by
            apply True.intro
          let assump_59 := assump_55 assump_89
          apply False.elim assump_59
        case inr assump_56 =>
          have assump_90 : True := by
            apply True.intro
          let assump_65 := assump_56 assump_90
          apply False.elim assump_65
    case inr assump_48 =>
      cases assump_46
      case inl assump_71 =>
        have assump_91 : True := by
          apply True.intro
        let assump_75 := assump_71 assump_91
        apply False.elim assump_75
      case inr assump_72 =>
        have assump_92 : True := by
          apply True.intro
        let assump_81 := assump_72 assump_92
        apply False.elim assump_81


variable (p6 p4 p2 p1 p5 p7 p3 : Prop)
theorem file74_91195 : (((((p3 ∨ p3) → (p5 → False)) ∧ ((p4 ∧ True) ∨ (p7 → False))) ∧ (((p3 ∨ True) ∨ (p3 → False)) → False)) → ((((p1 → False) → (p2 ∧ p1)) → ((p6 → False) → (p7 → False))) ∧ (((False ∧ True) ∨ (p3 → p2)) ∧ ((p4 → False) → (False → p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_1
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      cases assump_14
      case inl assump_17 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          have assump_79 : ((p3 ∨ True) ∨ (p3 → False)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_27 := assump_12 assump_79
          apply False.elim assump_27
      case inr assump_18 =>
        have assump_80 : ((p3 ∨ True) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_35 := assump_12 assump_80
        apply False.elim assump_35
  apply And.intro
  cases assump_1
  case intro assump_39 assump_40 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_42
      case inl assump_45 =>
        cases assump_45
        case intro assump_47 assump_48 =>
          apply Or.inr
          intro assump_55
          have assump_81 : ((p3 ∨ True) ∨ (p3 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_55
          let assump_59 := assump_40 assump_81
          apply False.elim assump_59
      case inr assump_46 =>
        apply Or.inr
        intro assump_67
        have assump_82 : ((p3 ∨ True) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_67
        let assump_71 := assump_40 assump_82
        apply False.elim assump_71
  intro assump_75
  intro assump_76
  apply False.elim assump_76


variable (p3 p0 p6 p5 p2 p4 p7 p1 : Prop)
theorem file74_93149 : (((((p5 → p1) → (True ∧ False)) → ((False → False) ∧ (p1 → False))) ∧ (((p7 → False) → (p7 ∨ p7)) → ((p3 ∧ False) → (p2 → False)))) ∨ ((((p2 → False) ∨ (False → p4)) → False) → (((p6 ∨ False) ∧ (p0 → False)) ∧ ((p3 → True) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  have assump_30 : (p5 → p1) := by
    intro assump_11
    exact assump_5
  let assump_10 := assump_1 assump_30
  let assump_14 := And.right assump_10
  apply False.elim assump_14
  intro assump_19
  intro assump_20
  intro assump_21
  cases assump_20
  case intro assump_24 assump_25 =>
    apply False.elim assump_25


variable (p7 p3 p0 p4 p2 p1 p5 : Prop)
theorem file74_93902 : ((((((p0 ∨ p1) ∧ (p2 ∨ p1)) → ((p7 ∧ p2) ∧ (p3 → False))) ∧ (((p1 ∨ p3) ∧ (p7 ∨ p3)) → ((p4 → True) → (p3 → False)))) ∧ ((((p2 ∨ p5) → (p5 ∧ p7)) → False) ∧ (((False ∧ True) → False) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        have assump_33 : ((False ∧ True) → False) := by
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
        let assump_24 := assump_19 assump_33
        apply False.elim assump_24


variable (p4 p0 p6 p3 p1 p7 : Prop)
theorem file74_94632 : (((((p1 ∨ p0) ∨ (p0 ∧ False)) → ((p3 ∧ False) → False)) → False) → ((((p4 ∧ p6) → False) ∧ ((p3 → False) → (p3 ∨ p3))) → (((False ∧ p0) ∨ (p7 ∨ p0)) ∨ ((p0 ∨ False) ∧ (True → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_23 : (((p1 ∨ p0) ∨ (p0 ∧ False)) → ((p3 ∧ False) → False)) := by
      intro assump_12
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_11 := assump_1 assump_23
    apply False.elim assump_11


variable (p6 p0 p2 p5 p4 p1 : Prop)
theorem file74_95262 : (((((p6 ∧ p1) → (p4 → p0)) ∧ ((p1 ∨ False) → (p1 ∧ p4))) → False) → ((((p1 ∨ p5) → (True → False)) → ((p0 → False) → (p0 ∧ p0))) → (((p1 → False) ∧ (False → p5)) → ((p4 ∨ p2) ∨ (False → True))))) := by
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply Or.inr
    intro assump_20
    apply True.intro


variable (p1 p5 p3 p0 p6 p2 p4 : Prop)
theorem file74_95689 : (((((p3 ∨ p2) → (p0 → False)) → ((p6 ∨ p6) → (p2 → p6))) → False) → ((((p4 ∧ False) → False) ∧ ((True → False) ∧ (p4 → False))) ∨ (((p1 ∨ p5) ∧ (p6 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6
  apply And.intro
  intro assump_11
  have assump_56 : (((p3 ∨ p2) → (p0 → False)) → ((p6 ∨ p6) → (p2 → p6))) := by
    intro assump_15
    intro assump_16
    intro assump_17
    cases assump_16
    case inl assump_20 =>
      exact assump_20
    case inr assump_21 =>
      exact assump_21
  let assump_14 := assump_1 assump_56
  apply False.elim assump_14
  intro assump_33
  have assump_57 : (((p3 ∨ p2) → (p0 → False)) → ((p6 ∨ p6) → (p2 → p6))) := by
    intro assump_38
    intro assump_39
    intro assump_40
    cases assump_39
    case inl assump_43 =>
      exact assump_43
    case inr assump_44 =>
      exact assump_44
  let assump_37 := assump_1 assump_57
  apply False.elim assump_37


variable (p4 p6 p2 p7 p1 : Prop)
theorem file74_96769 : ((((((p6 ∧ p4) → (p1 ∧ True)) → ((p2 ∨ p4) ∨ (True → True))) ∨ (((p1 → False) → (p7 ∧ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p6 ∧ p4) → (p1 ∧ True)) → ((p2 ∨ p4) ∨ (True → True))) ∨ (((p1 → False) → (p7 ∧ p1)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p3 p7 p6 p2 p0 p1 p4 : Prop)
theorem file74_97256 : (((((p7 ∧ p0) ∧ (p1 → p2)) → False) → (((p6 → p6) → False) → False)) ∨ ((((p2 ∨ False) → False) ∨ ((p7 ∨ False) ∧ (p1 → True))) ∨ (((True → p4) → (p4 ∨ p3)) → ((False → True) ∧ (p1 ∨ False))))) := by
  apply Or.inl
  intro assump_11
  intro assump_12
  have assump_25 : (p6 → p6) := by
    intro assump_19
    exact assump_19
  let assump_18 := assump_12 assump_25
  apply False.elim assump_18


variable (p1 p0 p5 p4 p3 : Prop)
theorem file74_97707 : (((((False → False) → False) ∧ ((p5 → False) ∧ (p3 ∧ p4))) → False) ∨ ((((p4 → False) → False) ∨ ((False ∧ p5) → (p0 ∧ p3))) → (((p0 → False) ∨ (True → False)) ∨ ((p4 → p1) → False)))) := by
  apply Or.inl
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      cases assump_22
      case intro assump_25 assump_26 =>
        have assump_41 : (False → False) := by
          intro assump_35
          apply False.elim assump_35
        let assump_34 := assump_17 assump_41
        apply False.elim assump_34


variable (p7 p6 p0 p4 p2 p1 : Prop)
theorem file74_98355 : ((((((p1 ∨ p4) → False) → False) → False) ∧ ((((p0 → True) ∨ (True → p2)) ∨ ((p7 → p6) ∨ (p7 → p4))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_23 : (((p0 → True) ∨ (True → p2)) ∨ ((p7 → p6) ∨ (p7 → p4))) := by
      apply Or.inl
      apply Or.inl
      intro assump_19
      apply True.intro
    let assump_18 := assump_13 assump_23
    apply False.elim assump_18


variable (p2 p1 p4 p0 p6 p5 : Prop)
theorem file74_98851 : (((((p0 ∧ False) → (p2 → False)) ∧ ((p5 ∨ p4) → False)) → (((p1 ∧ False) ∧ (p6 → False)) ∨ ((p4 ∧ p0) → False))) ∨ ((((p2 → False) → False) → False) → (((p0 ∨ True) → (p0 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_21 : (p5 ∨ p4) := by
        apply Or.inr
        exact assump_9
      let assump_17 := assump_3 assump_21
      apply False.elim assump_17


variable (p0 p5 p2 p4 : Prop)
theorem file74_99435 : ((((((p2 ∧ True) → (p4 → True)) ∧ ((p5 → True) ∨ (p2 ∨ p4))) ∨ (((p2 → p0) → False) → ((p2 → False) → (p5 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p2 ∧ True) → (p4 → True)) ∧ ((p5 → True) ∨ (p2 ∨ p4))) ∨ (((p2 → p0) → False) → ((p2 → False) → (p5 ∨ p0)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    apply True.intro
    apply Or.inl
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p1 p7 p5 p3 p6 p4 p0 : Prop)
theorem file74_100013 : (((((p3 ∧ p6) ∨ (p2 → p0)) → ((p5 → p2) ∨ (True ∧ False))) → (((False ∨ True) ∧ (p2 → p6)) → ((p1 ∧ p7) ∨ (True ∨ p6)))) ∨ ((((p6 ∨ p4) → (False → False)) → ((p0 → False) ∧ (True → p5))) ∨ (((True → False) ∨ (p7 → False)) ∧ ((p1 ∧ p4) → (True → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      apply Or.inr
      apply Or.inl
      apply True.intro


variable (p6 p2 p5 p1 p7 p0 : Prop)
theorem file74_100597 : (((((p5 ∨ p2) → (True ∨ False)) → False) ∧ (((p1 ∨ p1) ∧ (p7 → p5)) → ((p0 ∧ p0) ∨ (p0 ∨ p2)))) → ((((p6 → False) → (p5 ∧ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_23 : ((p5 ∨ p2) → (True ∨ False)) := by
      intro assump_13
      cases assump_13
      case inl assump_14 =>
        apply Or.inl
        apply True.intro
      case inr assump_15 =>
        apply Or.inl
        apply True.intro
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12


variable (p4 p7 p2 p6 p0 p3 p5 : Prop)
theorem file74_101216 : (((((p4 → p6) → False) ∧ ((False → p0) → False)) → (((p2 ∨ True) → (p7 ∧ p5)) → ((p5 → False) → False))) ∨ ((((p6 → False) → False) → ((False → p0) ∧ (p3 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    have assump_21 : (False → p0) := by
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_9 assump_21
    apply False.elim assump_14


variable (p0 p6 p3 p2 p5 p4 : Prop)
theorem file74_101737 : (((((p4 ∨ False) → False) → ((p4 ∨ p3) ∨ (p2 → p2))) → False) → ((((p6 ∧ p0) → (p3 ∨ p2)) → False) ∧ (((False ∧ p4) ∨ (p5 ∧ p5)) → False))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  have assump_46 : (((p4 ∨ False) → False) → ((p4 ∨ p3) ∨ (p2 → p2))) := by
    intro assump_12
    apply Or.inr
    intro assump_15
    exact assump_15
  let assump_11 := assump_5 assump_46
  apply False.elim assump_11
  intro assump_21
  cases assump_21
  case inl assump_22 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      apply False.elim assump_24
  case inr assump_23 =>
    cases assump_23
    case intro assump_28 assump_29 =>
      have assump_47 : (((p4 ∨ False) → False) → ((p4 ∨ p3) ∨ (p2 → p2))) := by
        intro assump_37
        apply Or.inr
        intro assump_40
        exact assump_40
      let assump_36 := assump_5 assump_47
      apply False.elim assump_36


variable (p3 p1 : Prop)
theorem file74_102684 : ((((((False → False) ∨ (p1 ∨ p3)) → False) → False) → False) → False) := by
  intro assump_9
  have assump_26 : ((((False → False) ∨ (p1 ∨ p3)) → False) → False) := by
    intro assump_13
    have assump_27 : ((False → False) ∨ (p1 ∨ p3)) := by
      apply Or.inl
      intro assump_17
      apply False.elim assump_17
    let assump_16 := assump_13 assump_27
    apply False.elim assump_16
  let assump_12 := assump_9 assump_26
  apply False.elim assump_12


variable (p5 p0 p4 p7 p6 p1 : Prop)
theorem file74_103202 : ((((((False ∨ p4) → False) ∨ ((p7 → False) ∨ (p1 ∨ True))) ∧ (((False ∧ False) ∨ (p1 ∧ p0)) → False)) ∧ ((((p4 → False) ∧ (p5 → False)) ∧ ((p4 ∧ p7) ∧ (p4 → False))) ∧ (((p1 ∨ p6) ∨ (False → False)) ∨ ((True → False) ∧ (True ∨ True))))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_22
      case inl assump_24 =>
        cases assump_21
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              cases assump_33
              case intro assump_40 assump_41 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  cases assump_31
                  case inl assump_50 =>
                    cases assump_50
                    case inl assump_52 =>
                      cases assump_52
                      case inl assump_54 =>
                        have assump_306 : p4 := by
                          exact assump_42
                        let assump_59 := assump_41 assump_306
                        apply False.elim assump_59
                      case inr assump_55 =>
                        have assump_307 : p4 := by
                          exact assump_42
                        let assump_66 := assump_41 assump_307
                        apply False.elim assump_66
                    case inr assump_53 =>
                      have assump_308 : p4 := by
                        exact assump_42
                      let assump_73 := assump_41 assump_308
                      apply False.elim assump_73
                  case inr assump_51 =>
                    cases assump_51
                    case intro assump_77 assump_78 =>
                      cases assump_78
                      case inl assump_81 =>
                        have assump_309 : True := by
                          apply True.intro
                        let assump_85 := assump_77 assump_309
                        apply False.elim assump_85
                      case inr assump_82 =>
                        have assump_310 : True := by
                          apply True.intro
                        let assump_91 := assump_77 assump_310
                        apply False.elim assump_91
      case inr assump_25 =>
        cases assump_25
        case inl assump_95 =>
          cases assump_21
          case intro assump_101 assump_102 =>
            cases assump_101
            case intro assump_103 assump_104 =>
              cases assump_103
              case intro assump_105 assump_106 =>
                cases assump_104
                case intro assump_111 assump_112 =>
                  cases assump_111
                  case intro assump_113 assump_114 =>
                    cases assump_102
                    case inl assump_121 =>
                      cases assump_121
                      case inl assump_123 =>
                        cases assump_123
                        case inl assump_125 =>
                          have assump_311 : p4 := by
                            exact assump_113
                          let assump_130 := assump_112 assump_311
                          apply False.elim assump_130
                        case inr assump_126 =>
                          have assump_312 : p4 := by
                            exact assump_113
                          let assump_137 := assump_112 assump_312
                          apply False.elim assump_137
                      case inr assump_124 =>
                        have assump_313 : p4 := by
                          exact assump_113
                        let assump_144 := assump_112 assump_313
                        apply False.elim assump_144
                    case inr assump_122 =>
                      cases assump_122
                      case intro assump_148 assump_149 =>
                        cases assump_149
                        case inl assump_152 =>
                          have assump_314 : True := by
                            apply True.intro
                          let assump_156 := assump_148 assump_314
                          apply False.elim assump_156
                        case inr assump_153 =>
                          have assump_315 : True := by
                            apply True.intro
                          let assump_162 := assump_148 assump_315
                          apply False.elim assump_162
        case inr assump_96 =>
          cases assump_96
          case inl assump_166 =>
            cases assump_21
            case intro assump_172 assump_173 =>
              cases assump_172
              case intro assump_174 assump_175 =>
                cases assump_174
                case intro assump_176 assump_177 =>
                  cases assump_175
                  case intro assump_182 assump_183 =>
                    cases assump_182
                    case intro assump_184 assump_185 =>
                      cases assump_173
                      case inl assump_192 =>
                        cases assump_192
                        case inl assump_194 =>
                          cases assump_194
                          case inl assump_196 =>
                            have assump_316 : p4 := by
                              exact assump_184
                            let assump_201 := assump_183 assump_316
                            apply False.elim assump_201
                          case inr assump_197 =>
                            have assump_317 : p4 := by
                              exact assump_184
                            let assump_208 := assump_183 assump_317
                            apply False.elim assump_208
                        case inr assump_195 =>
                          have assump_318 : p4 := by
                            exact assump_184
                          let assump_215 := assump_183 assump_318
                          apply False.elim assump_215
                      case inr assump_193 =>
                        cases assump_193
                        case intro assump_219 assump_220 =>
                          cases assump_220
                          case inl assump_223 =>
                            have assump_319 : True := by
                              apply True.intro
                            let assump_227 := assump_219 assump_319
                            apply False.elim assump_227
                          case inr assump_224 =>
                            have assump_320 : True := by
                              apply True.intro
                            let assump_233 := assump_219 assump_320
                            apply False.elim assump_233
          case inr assump_167 =>
            cases assump_21
            case intro assump_241 assump_242 =>
              cases assump_241
              case intro assump_243 assump_244 =>
                cases assump_243
                case intro assump_245 assump_246 =>
                  cases assump_244
                  case intro assump_251 assump_252 =>
                    cases assump_251
                    case intro assump_253 assump_254 =>
                      cases assump_242
                      case inl assump_261 =>
                        cases assump_261
                        case inl assump_263 =>
                          cases assump_263
                          case inl assump_265 =>
                            have assump_321 : p4 := by
                              exact assump_253
                            let assump_270 := assump_252 assump_321
                            apply False.elim assump_270
                          case inr assump_266 =>
                            have assump_322 : p4 := by
                              exact assump_253
                            let assump_277 := assump_252 assump_322
                            apply False.elim assump_277
                        case inr assump_264 =>
                          have assump_323 : p4 := by
                            exact assump_253
                          let assump_284 := assump_252 assump_323
                          apply False.elim assump_284
                      case inr assump_262 =>
                        cases assump_262
                        case intro assump_288 assump_289 =>
                          cases assump_289
                          case inl assump_292 =>
                            have assump_324 : True := by
                              apply True.intro
                            let assump_296 := assump_288 assump_324
                            apply False.elim assump_296
                          case inr assump_293 =>
                            have assump_325 : True := by
                              apply True.intro
                            let assump_302 := assump_288 assump_325
                            apply False.elim assump_302


variable (p1 p0 p7 p2 p3 p4 : Prop)
theorem file74_112375 : (((((False ∧ False) → False) → False) ∧ (((p3 ∨ p4) ∧ (p2 → True)) ∨ ((p0 → p2) ∨ (p7 ∨ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_82 : ((False ∧ False) → False) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              apply False.elim assump_20
          let assump_18 := assump_2 assump_82
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_83 : ((False ∧ False) → False) := by
            intro assump_34
            cases assump_34
            case intro assump_35 assump_36 =>
              apply False.elim assump_35
          let assump_33 := assump_2 assump_83
          apply False.elim assump_33
    case inr assump_7 =>
      cases assump_7
      case inl assump_42 =>
        have assump_84 : ((False ∧ False) → False) := by
          intro assump_48
          cases assump_48
          case intro assump_49 assump_50 =>
            apply False.elim assump_49
        let assump_47 := assump_2 assump_84
        apply False.elim assump_47
      case inr assump_43 =>
        cases assump_43
        case inl assump_56 =>
          have assump_85 : ((False ∧ False) → False) := by
            intro assump_62
            cases assump_62
            case intro assump_63 assump_64 =>
              apply False.elim assump_63
          let assump_61 := assump_2 assump_85
          apply False.elim assump_61
        case inr assump_57 =>
          have assump_86 : ((False ∧ False) → False) := by
            intro assump_74
            cases assump_74
            case intro assump_75 assump_76 =>
              apply False.elim assump_75
          let assump_73 := assump_2 assump_86
          apply False.elim assump_73


variable (p0 p1 p2 p7 : Prop)
theorem file74_114390 : (((((p1 → False) ∧ (p2 ∧ p1)) → False) → False) → ((((False → False) ∧ (p1 → False)) ∧ ((p0 ∧ p0) → (p7 → False))) ∧ (((p0 → p0) ∨ (p0 → False)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  have assump_117 : (((p1 → False) ∧ (p2 ∧ p1)) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        have assump_118 : p1 := by
          exact assump_17
        let assump_24 := assump_12 assump_118
        apply False.elim assump_24
  let assump_10 := assump_1 assump_117
  apply False.elim assump_10
  intro assump_31
  intro assump_32
  cases assump_31
  case intro assump_35 assump_36 =>
    have assump_119 : (((p1 → False) ∧ (p2 ∧ p1)) → False) := by
      intro assump_44
      cases assump_44
      case intro assump_45 assump_46 =>
        cases assump_46
        case intro assump_49 assump_50 =>
          have assump_120 : p1 := by
            exact assump_50
          let assump_57 := assump_45 assump_120
          apply False.elim assump_57
    let assump_43 := assump_1 assump_119
    apply False.elim assump_43
  intro assump_64
  cases assump_64
  case inl assump_65 =>
    have assump_121 : (((p1 → False) ∧ (p2 ∧ p1)) → False) := by
      intro assump_72
      cases assump_72
      case intro assump_73 assump_74 =>
        cases assump_74
        case intro assump_77 assump_78 =>
          have assump_122 : p1 := by
            exact assump_78
          let assump_85 := assump_73 assump_122
          apply False.elim assump_85
    let assump_71 := assump_1 assump_121
    apply False.elim assump_71
  case inr assump_66 =>
    have assump_123 : (((p1 → False) ∧ (p2 ∧ p1)) → False) := by
      intro assump_97
      cases assump_97
      case intro assump_98 assump_99 =>
        cases assump_99
        case intro assump_102 assump_103 =>
          have assump_124 : p1 := by
            exact assump_103
          let assump_110 := assump_98 assump_124
          apply False.elim assump_110
    let assump_96 := assump_1 assump_123
    apply False.elim assump_96


variable (p2 p1 p6 p7 p4 p3 p5 p0 : Prop)
theorem file74_116654 : (((((p4 ∨ p0) ∨ (p2 → False)) → False) ∧ (((p3 → False) → (p3 → False)) → False)) → ((((p2 ∧ p2) ∧ (p6 ∧ False)) → ((p1 → False) → (p5 → p6))) → (((p7 → False) → (p3 ∧ p3)) ∨ ((True → False) ∧ (p5 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    apply And.intro
    have assump_46 : ((p3 → False) → (p3 → False)) := by
      intro assump_16
      intro assump_17
      have assump_47 : p3 := by
        exact assump_17
      let assump_22 := assump_16 assump_47
      apply False.elim assump_22
    let assump_15 := assump_6 assump_46
    apply False.elim assump_15
    have assump_48 : ((p3 → False) → (p3 → False)) := by
      intro assump_33
      intro assump_34
      have assump_49 : p3 := by
        exact assump_34
      let assump_39 := assump_33 assump_49
      apply False.elim assump_39
    let assump_32 := assump_6 assump_48
    apply False.elim assump_32


variable (p6 p0 p7 p2 p4 p5 p3 p1 : Prop)
theorem file74_117683 : ((((((p0 ∨ p2) ∨ (p2 → p1)) ∧ ((p1 → p6) ∨ (p4 ∨ p3))) ∨ (((p0 ∨ p5) ∨ (p4 ∨ p2)) ∨ ((p2 → True) ∧ (True ∨ p2)))) ∧ ((((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case inl assump_14 =>
              have assump_269 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                apply Or.inl
                intro assump_21
                cases assump_21
                case inl assump_22 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_23 =>
                  apply Or.inr
                  apply True.intro
              let assump_20 := assump_3 assump_269
              apply False.elim assump_20
            case inr assump_15 =>
              cases assump_15
              case inl assump_31 =>
                have assump_270 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                  apply Or.inl
                  intro assump_38
                  cases assump_38
                  case inl assump_39 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_40 =>
                    apply Or.inr
                    apply True.intro
                let assump_37 := assump_3 assump_270
                apply False.elim assump_37
              case inr assump_32 =>
                have assump_271 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                  apply Or.inl
                  intro assump_53
                  cases assump_53
                  case inl assump_54 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_55 =>
                    apply Or.inr
                    apply True.intro
                let assump_52 := assump_3 assump_271
                apply False.elim assump_52
          case inr assump_11 =>
            cases assump_7
            case inl assump_65 =>
              have assump_272 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                apply Or.inl
                intro assump_72
                cases assump_72
                case inl assump_73 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_74 =>
                  apply Or.inr
                  apply True.intro
              let assump_71 := assump_3 assump_272
              apply False.elim assump_71
            case inr assump_66 =>
              cases assump_66
              case inl assump_82 =>
                have assump_273 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                  apply Or.inl
                  intro assump_89
                  cases assump_89
                  case inl assump_90 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_91 =>
                    apply Or.inr
                    apply True.intro
                let assump_88 := assump_3 assump_273
                apply False.elim assump_88
              case inr assump_83 =>
                have assump_274 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                  apply Or.inl
                  intro assump_104
                  cases assump_104
                  case inl assump_105 =>
                    apply Or.inr
                    apply True.intro
                  case inr assump_106 =>
                    apply Or.inr
                    apply True.intro
                let assump_103 := assump_3 assump_274
                apply False.elim assump_103
        case inr assump_9 =>
          cases assump_7
          case inl assump_116 =>
            have assump_275 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_123
              cases assump_123
              case inl assump_124 =>
                apply Or.inr
                apply True.intro
              case inr assump_125 =>
                apply Or.inr
                apply True.intro
            let assump_122 := assump_3 assump_275
            apply False.elim assump_122
          case inr assump_117 =>
            cases assump_117
            case inl assump_133 =>
              have assump_276 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                apply Or.inl
                intro assump_140
                cases assump_140
                case inl assump_141 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_142 =>
                  apply Or.inr
                  apply True.intro
              let assump_139 := assump_3 assump_276
              apply False.elim assump_139
            case inr assump_134 =>
              have assump_277 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
                apply Or.inl
                intro assump_155
                cases assump_155
                case inl assump_156 =>
                  apply Or.inr
                  apply True.intro
                case inr assump_157 =>
                  apply Or.inr
                  apply True.intro
              let assump_154 := assump_3 assump_277
              apply False.elim assump_154
    case inr assump_5 =>
      cases assump_5
      case inl assump_165 =>
        cases assump_165
        case inl assump_167 =>
          cases assump_167
          case inl assump_169 =>
            have assump_278 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_176
              cases assump_176
              case inl assump_177 =>
                apply Or.inr
                apply True.intro
              case inr assump_178 =>
                apply Or.inr
                apply True.intro
            let assump_175 := assump_3 assump_278
            apply False.elim assump_175
          case inr assump_170 =>
            have assump_279 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_191
              cases assump_191
              case inl assump_192 =>
                apply Or.inr
                apply True.intro
              case inr assump_193 =>
                apply Or.inr
                apply True.intro
            let assump_190 := assump_3 assump_279
            apply False.elim assump_190
        case inr assump_168 =>
          cases assump_168
          case inl assump_201 =>
            have assump_280 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_208
              cases assump_208
              case inl assump_209 =>
                apply Or.inr
                apply True.intro
              case inr assump_210 =>
                apply Or.inr
                apply True.intro
            let assump_207 := assump_3 assump_280
            apply False.elim assump_207
          case inr assump_202 =>
            have assump_281 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_223
              cases assump_223
              case inl assump_224 =>
                apply Or.inr
                apply True.intro
              case inr assump_225 =>
                apply Or.inr
                apply True.intro
            let assump_222 := assump_3 assump_281
            apply False.elim assump_222
      case inr assump_166 =>
        cases assump_166
        case intro assump_233 assump_234 =>
          cases assump_234
          case inl assump_237 =>
            have assump_282 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_244
              cases assump_244
              case inl assump_245 =>
                apply Or.inr
                apply True.intro
              case inr assump_246 =>
                apply Or.inr
                apply True.intro
            let assump_243 := assump_3 assump_282
            apply False.elim assump_243
          case inr assump_238 =>
            have assump_283 : (((p1 ∨ True) → (p7 ∨ True)) ∨ ((p2 → p6) → (p5 → p7))) := by
              apply Or.inl
              intro assump_259
              cases assump_259
              case inl assump_260 =>
                apply Or.inr
                apply True.intro
              case inr assump_261 =>
                apply Or.inr
                apply True.intro
            let assump_258 := assump_3 assump_283
            apply False.elim assump_258


variable (p7 p6 : Prop)
theorem file74_126686 : (((((True → False) ∧ (p6 ∧ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_25 : (((True → False) ∧ (p6 ∧ p7)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p4 p6 p7 : Prop)
theorem file74_127228 : ((((((p7 ∧ p6) ∧ (True → False)) ∧ ((True → False) ∧ (False → False))) → (((p4 → p0) → (p4 → False)) ∧ ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_64 : ((((p7 ∧ p6) ∧ (True → False)) ∧ ((True → False) ∧ (False → False))) → (((p4 → p0) → (p4 → False)) ∧ ((p7 → False) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_13
          case intro assump_24 assump_25 =>
            have assump_65 : True := by
              apply True.intro
            let assump_31 := assump_24 assump_65
            apply False.elim assump_31
    intro assump_35
    cases assump_5
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          cases assump_39
          case intro assump_50 assump_51 =>
            have assump_66 : True := by
              apply True.intro
            let assump_57 := assump_50 assump_66
            apply False.elim assump_57
  let assump_4 := assump_1 assump_64
  apply False.elim assump_4


variable (p2 p4 p7 p6 p3 p0 : Prop)
theorem file74_128598 : (((((False → False) → (p7 → p4)) → ((True → p3) → (p7 ∧ p7))) ∧ (((True ∨ p6) ∧ (p7 → False)) ∧ ((p4 → True) → (p4 → True)))) → ((((p2 ∧ p6) ∨ (p7 ∨ False)) ∨ ((True ∧ False) → (True ∧ p2))) ∨ (((p4 → False) → (p0 ∨ p6)) → ((False → False) ∨ (True ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          apply Or.inr
          intro assump_18
          apply And.intro
          apply True.intro
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        case inr assump_11 =>
          apply Or.inl
          apply Or.inr
          intro assump_31
          apply And.intro
          apply True.intro
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_33


