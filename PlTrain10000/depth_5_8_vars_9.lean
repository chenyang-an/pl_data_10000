variable (p7 p6 p4 p5 p3 p0 : Prop)
theorem file9_44 : ((((((p4 ∧ p3) ∨ (p7 ∧ p4)) → ((p5 → True) → (False → False))) ∨ (((p6 → p7) ∧ (p5 → False)) ∧ ((p4 → p0) ∨ (True → True)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p4 ∧ p3) ∨ (p7 ∧ p4)) → ((p5 → True) → (False → False))) ∨ (((p6 → p7) ∧ (p5 → False)) ∧ ((p4 → p0) ∨ (True → True)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p6 p1 p4 p3 p2 p0 : Prop)
theorem file9_590 : (((((p2 ∧ True) → (p2 ∨ p1)) ∧ ((p1 → p4) → (False → False))) → False) → ((((p0 ∧ p1) → (p1 → False)) ∧ ((True → p3) → False)) → (((p7 ∧ p4) → False) → ((p6 ∨ p7) → (True → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_2
    case intro assump_14 assump_15 =>
      have assump_64 : (((p2 ∧ True) → (p2 ∨ p1)) ∧ ((p1 → p4) → (False → False))) := by
        apply And.intro
        intro assump_23
        cases assump_23
        case intro assump_24 assump_25 =>
          apply Or.inl
          exact assump_24
        intro assump_30
        intro assump_31
        apply False.elim assump_31
      let assump_22 := assump_1 assump_64
      apply False.elim assump_22
  case inr assump_9 =>
    cases assump_2
    case intro assump_41 assump_42 =>
      have assump_65 : (((p2 ∧ True) → (p2 ∨ p1)) ∧ ((p1 → p4) → (False → False))) := by
        apply And.intro
        intro assump_50
        cases assump_50
        case intro assump_51 assump_52 =>
          apply Or.inl
          exact assump_51
        intro assump_57
        intro assump_58
        apply False.elim assump_58
      let assump_49 := assump_1 assump_65
      apply False.elim assump_49


variable (p2 p1 p5 p4 p6 : Prop)
theorem file9_1919 : (((((p4 ∨ p6) ∨ (False → p2)) ∧ ((True → False) → False)) ∧ (((p5 ∨ p1) ∨ (p4 ∨ p4)) ∧ ((p2 → True) ∧ (False ∧ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_15
                case intro assump_22 assump_23 =>
                  cases assump_23
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
              case inr assump_19 =>
                cases assump_15
                case intro assump_32 assump_33 =>
                  cases assump_33
                  case intro assump_36 assump_37 =>
                    apply False.elim assump_36
            case inr assump_17 =>
              cases assump_17
              case inl assump_40 =>
                cases assump_15
                case intro assump_44 assump_45 =>
                  cases assump_45
                  case intro assump_48 assump_49 =>
                    apply False.elim assump_48
              case inr assump_41 =>
                cases assump_15
                case intro assump_54 assump_55 =>
                  cases assump_55
                  case intro assump_58 assump_59 =>
                    apply False.elim assump_58
        case inr assump_9 =>
          cases assump_3
          case intro assump_66 assump_67 =>
            cases assump_66
            case inl assump_68 =>
              cases assump_68
              case inl assump_70 =>
                cases assump_67
                case intro assump_74 assump_75 =>
                  cases assump_75
                  case intro assump_78 assump_79 =>
                    apply False.elim assump_78
              case inr assump_71 =>
                cases assump_67
                case intro assump_84 assump_85 =>
                  cases assump_85
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_88
            case inr assump_69 =>
              cases assump_69
              case inl assump_92 =>
                cases assump_67
                case intro assump_96 assump_97 =>
                  cases assump_97
                  case intro assump_100 assump_101 =>
                    apply False.elim assump_100
              case inr assump_93 =>
                cases assump_67
                case intro assump_106 assump_107 =>
                  cases assump_107
                  case intro assump_110 assump_111 =>
                    apply False.elim assump_110
      case inr assump_7 =>
        cases assump_3
        case intro assump_118 assump_119 =>
          cases assump_118
          case inl assump_120 =>
            cases assump_120
            case inl assump_122 =>
              cases assump_119
              case intro assump_126 assump_127 =>
                cases assump_127
                case intro assump_130 assump_131 =>
                  apply False.elim assump_130
            case inr assump_123 =>
              cases assump_119
              case intro assump_136 assump_137 =>
                cases assump_137
                case intro assump_140 assump_141 =>
                  apply False.elim assump_140
          case inr assump_121 =>
            cases assump_121
            case inl assump_144 =>
              cases assump_119
              case intro assump_148 assump_149 =>
                cases assump_149
                case intro assump_152 assump_153 =>
                  apply False.elim assump_152
            case inr assump_145 =>
              cases assump_119
              case intro assump_158 assump_159 =>
                cases assump_159
                case intro assump_162 assump_163 =>
                  apply False.elim assump_162


variable (p2 p0 p6 p4 p7 p3 p5 : Prop)
theorem file9_6067 : (((((p5 ∨ False) ∨ (p2 ∨ p2)) → ((p2 ∨ p3) → (False ∧ p3))) ∧ (((p0 → False) ∧ (p2 ∧ p6)) ∧ ((p4 → False) ∧ (False → True)))) → ((((p2 ∨ p5) ∧ (p5 → p7)) → False) ∧ (((p4 ∧ p4) ∨ (p7 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              cases assump_16
              case intro assump_27 assump_28 =>
                have assump_152 : ((p5 ∨ False) ∨ (p2 ∨ p2)) := by
                  apply Or.inr
                  apply Or.inl
                  exact assump_21
                let assump_38 := assump_11 assump_152
                have assump_153 : (p2 ∨ p3) := by
                  apply Or.inl
                  exact assump_21
                let assump_39 := assump_38 assump_153
                let assump_40 := And.left assump_39
                apply False.elim assump_40
    case inr assump_6 =>
      cases assump_1
      case intro assump_48 assump_49 =>
        cases assump_49
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              cases assump_53
              case intro assump_64 assump_65 =>
                have assump_154 : ((p5 ∨ False) ∨ (p2 ∨ p2)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_6
                let assump_75 := assump_48 assump_154
                have assump_155 : (p2 ∨ p3) := by
                  apply Or.inl
                  exact assump_58
                let assump_76 := assump_75 assump_155
                let assump_77 := And.left assump_76
                apply False.elim assump_77
  intro assump_81
  cases assump_81
  case inl assump_82 =>
    cases assump_82
    case intro assump_84 assump_85 =>
      cases assump_1
      case intro assump_90 assump_91 =>
        cases assump_91
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            cases assump_97
            case intro assump_100 assump_101 =>
              cases assump_95
              case intro assump_106 assump_107 =>
                have assump_156 : p4 := by
                  exact assump_85
                let assump_113 := assump_106 assump_156
                apply False.elim assump_113
  case inr assump_83 =>
    cases assump_1
    case intro assump_119 assump_120 =>
      cases assump_120
      case intro assump_123 assump_124 =>
        cases assump_123
        case intro assump_125 assump_126 =>
          cases assump_126
          case intro assump_129 assump_130 =>
            cases assump_124
            case intro assump_135 assump_136 =>
              have assump_157 : ((p5 ∨ False) ∨ (p2 ∨ p2)) := by
                apply Or.inr
                apply Or.inl
                exact assump_129
              let assump_146 := assump_119 assump_157
              have assump_158 : (p2 ∨ p3) := by
                apply Or.inl
                exact assump_129
              let assump_147 := assump_146 assump_158
              let assump_148 := And.left assump_147
              apply False.elim assump_148


variable (p3 p6 p5 p2 p7 : Prop)
theorem file9_9648 : ((((((p6 ∧ p7) → False) → ((p5 → False) ∧ (p3 ∨ p6))) ∧ (((p6 → p5) ∧ (p5 ∧ p5)) → ((p3 ∨ p3) → (p5 → False)))) ∧ ((((p2 ∧ p3) ∧ (p3 → False)) → False) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      have assump_48 : (((p2 ∧ p3) ∧ (p3 → False)) → False) := by
        intro assump_30
        cases assump_30
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            have assump_49 : p3 := by
              exact assump_34
            let assump_41 := assump_32 assump_49
            apply False.elim assump_41
      let assump_29 := assump_20 assump_48
      apply False.elim assump_29


variable (p2 p5 p7 : Prop)
theorem file9_10464 : ((((((p7 → False) ∨ (p5 → False)) → False) → False) ∧ ((((True → False) → (True ∨ p2)) → ((False ∧ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((True → False) → (True ∨ p2)) → ((False ∧ p7) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p3 p1 p0 p6 p2 p5 : Prop)
theorem file9_11024 : (((((p5 ∨ True) ∧ (p5 → p6)) ∧ ((p3 ∧ p0) ∧ (True → False))) ∧ (((p5 → p1) ∧ (False → True)) ∧ ((p2 ∧ False) ∧ (False ∨ p2)))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  cases assump_25
                  case intro assump_32 assump_33 =>
                    cases assump_32
                    case intro assump_34 assump_35 =>
                      apply False.elim assump_35
        case inr assump_9 =>
          cases assump_5
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              cases assump_3
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  cases assump_55
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case intro assump_64 assump_65 =>
                      apply False.elim assump_65


variable (p1 p6 p0 p4 p7 : Prop)
theorem file9_12540 : (((((p4 → False) → (p6 → False)) ∧ ((p1 → p4) → False)) → (((p0 ∧ False) ∧ (p6 → True)) → False)) ∨ ((((p4 → False) → False) ∨ ((False ∧ p6) ∨ (False ∧ p7))) → (((p6 → p1) ∨ (p7 → p1)) ∨ ((False ∧ True) ∧ (p4 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p6 p2 p1 p4 p3 p0 p7 : Prop)
theorem file9_13017 : (((((p7 → False) → (p4 ∨ p4)) → ((p0 → p3) → False)) ∧ (((p3 ∧ p4) ∧ (p1 ∨ True)) ∨ ((p7 → p7) → False))) → ((((p1 → False) → False) ∧ ((p4 ∨ True) ∧ (False ∧ p1))) → (((p4 ∨ True) ∧ (p2 → p1)) ∨ ((p6 → p7) ∧ (p3 ∧ p7))))) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_12
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
      case inr assump_14 =>
        cases assump_12
        case intro assump_23 assump_24 =>
          apply False.elim assump_23


variable (p1 p6 p2 p4 p3 p0 : Prop)
theorem file9_13732 : ((((((p6 → False) ∨ (p1 → False)) ∧ ((p4 → p4) → False)) ∧ (((p3 → p0) → False) → False)) ∧ ((((True ∨ True) ∨ (False → p4)) → False) ∧ (((p2 → False) ∨ (p1 → False)) ∨ ((True → False) ∨ (p3 → True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                have assump_96 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_27 := assump_16 assump_96
                apply False.elim assump_27
              case inr assump_23 =>
                have assump_97 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_34 := assump_16 assump_97
                apply False.elim assump_34
            case inr assump_21 =>
              cases assump_21
              case inl assump_38 =>
                have assump_98 : True := by
                  apply True.intro
                let assump_42 := assump_38 assump_98
                apply False.elim assump_42
              case inr assump_39 =>
                have assump_99 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_49 := assump_16 assump_99
                apply False.elim assump_49
        case inr assump_9 =>
          cases assump_3
          case intro assump_59 assump_60 =>
            cases assump_60
            case inl assump_63 =>
              cases assump_63
              case inl assump_65 =>
                have assump_100 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_70 := assump_59 assump_100
                apply False.elim assump_70
              case inr assump_66 =>
                have assump_101 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_77 := assump_59 assump_101
                apply False.elim assump_77
            case inr assump_64 =>
              cases assump_64
              case inl assump_81 =>
                have assump_102 : True := by
                  apply True.intro
                let assump_85 := assump_81 assump_102
                apply False.elim assump_85
              case inr assump_82 =>
                have assump_103 : ((True ∨ True) ∨ (False → p4)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_92 := assump_59 assump_103
                apply False.elim assump_92


variable (p3 p7 p2 p5 p6 p0 p4 : Prop)
theorem file9_16950 : (((((p6 ∧ True) → (False → p7)) → False) ∨ (((True → p7) ∧ (p3 → p3)) → False)) → ((((True ∨ p4) ∧ (p0 ∧ p3)) ∨ ((p4 ∧ p3) → (p5 → p4))) ∨ (((p6 → False) ∧ (p2 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_10
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_18
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      exact assump_22


variable (p6 p2 p3 p1 p4 p0 p5 p7 : Prop)
theorem file9_17588 : ((((((False ∧ True) ∨ (p1 ∧ False)) → ((p6 → False) ∨ (p6 → False))) → (((p7 ∨ p0) ∧ (p4 ∧ p4)) ∨ ((p1 ∧ False) ∧ (p2 ∧ True)))) ∧ ((((False ∨ True) ∨ (False → False)) → False) ∧ (((p6 ∨ p6) → False) ∨ ((p3 ∨ p5) ∨ (p0 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_44 : ((False ∨ True) ∨ (False → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_15 := assump_6 assump_44
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case inl assump_19 =>
          cases assump_19
          case inl assump_21 =>
            have assump_45 : ((False ∨ True) ∨ (False → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_26 := assump_6 assump_45
            apply False.elim assump_26
          case inr assump_22 =>
            have assump_46 : ((False ∨ True) ∨ (False → False)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_33 := assump_6 assump_46
            apply False.elim assump_33
        case inr assump_20 =>
          have assump_47 : ((False ∨ True) ∨ (False → False)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_40 := assump_6 assump_47
          apply False.elim assump_40


variable (p6 p1 p3 p4 : Prop)
theorem file9_19195 : (((((False → False) ∧ (True → False)) ∧ ((False ∧ p1) → False)) ∧ (((p6 ∧ p4) ∧ (p3 ∨ p4)) → ((p6 ∨ False) ∨ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_22 : True := by
          apply True.intro
        let assump_18 := assump_7 assump_22
        apply False.elim assump_18


variable (p1 p2 p7 p3 p5 : Prop)
theorem file9_19716 : ((((((p7 ∨ p3) ∧ (p1 ∨ p2)) ∨ ((True ∧ p5) ∧ (p3 → False))) → False) ∧ ((((False → False) ∧ (False → False)) ∧ ((p2 ∨ p2) ∧ (p1 ∨ p5))) ∧ (((True ∨ True) ∨ (True → False)) → False))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_19
          case intro assump_26 assump_27 =>
            cases assump_26
            case inl assump_28 =>
              cases assump_27
              case inl assump_32 =>
                have assump_70 : ((True ∨ True) ∨ (True → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_38 := assump_17 assump_70
                apply False.elim assump_38
              case inr assump_33 =>
                have assump_71 : ((True ∨ True) ∨ (True → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_46 := assump_17 assump_71
                apply False.elim assump_46
            case inr assump_29 =>
              cases assump_27
              case inl assump_52 =>
                have assump_72 : ((True ∨ True) ∨ (True → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_58 := assump_17 assump_72
                apply False.elim assump_58
              case inr assump_53 =>
                have assump_73 : ((True ∨ True) ∨ (True → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_66 := assump_17 assump_73
                apply False.elim assump_66


variable (p5 p6 p7 p3 p4 p0 : Prop)
theorem file9_21662 : ((((((p3 ∧ p3) → (p7 ∧ p4)) → ((p5 ∨ p6) → (False → p0))) ∨ (((p7 → p5) → False) ∧ ((p7 → p6) ∧ (p3 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p3 ∧ p3) → (p7 ∧ p4)) → ((p5 ∨ p6) → (False → p0))) ∨ (((p7 → p5) → False) ∧ ((p7 → p6) ∧ (p3 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p4 p2 p6 p1 : Prop)
theorem file9_22170 : ((((((False ∧ p6) → (p1 ∧ p4)) → ((p6 → False) → (p4 ∧ True))) → False) ∧ ((((p2 ∧ True) ∧ (p6 → p3)) ∨ ((p4 → False) → (p1 → p6))) ∧ (((False → False) ∨ (p2 → False)) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            have assump_40 : ((False → False) ∨ (p2 → False)) := by
              apply Or.inl
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_7 assump_40
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_41 : ((False → False) ∨ (p2 → False)) := by
          apply Or.inl
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_7 assump_41
        apply False.elim assump_33


variable (p0 p6 p1 p2 p4 : Prop)
theorem file9_23236 : ((((((False → False) ∨ (p1 → False)) ∧ ((p6 ∧ p0) → False)) → False) ∧ ((((p2 ∧ False) → (False → False)) ∨ ((p1 → p4) ∧ (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p2 ∧ False) → (False → False)) ∨ ((p1 → p4) ∧ (p0 → False))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p2 p7 p6 p5 p3 : Prop)
theorem file9_23777 : (((((False → p3) ∨ (p2 → False)) ∨ ((p5 ∨ True) → False)) ∨ (((True → p6) → False) → False)) ∧ ((((p7 → True) ∨ (True → False)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  intro assump_4
  have assump_12 : ((p7 → True) ∨ (True → False)) := by
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_7 := assump_4 assump_12
  apply False.elim assump_7


variable (p0 p6 p2 p7 : Prop)
theorem file9_24287 : (((((p7 → False) ∨ (p0 ∧ p0)) → False) ∧ (((p6 → p2) ∨ (p6 → False)) ∧ ((p7 ∧ False) ∧ (p2 ∨ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
      case inr assump_9 =>
        cases assump_7
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            apply False.elim assump_25


variable (p2 p4 p0 p7 p1 p6 p5 : Prop)
theorem file9_25011 : (((((p4 ∧ p4) ∧ (p1 ∨ p6)) ∧ ((p0 → p5) ∧ (p0 → False))) → (((p1 ∨ p7) ∧ (p4 → False)) → ((p5 → False) → (p6 ∧ p0)))) ∨ ((((p4 → p2) ∧ (p0 → False)) ∧ ((p4 → True) → (p6 ∧ p2))) → False)) := by
  apply Or.inl
  intro assump_17
  intro assump_18
  intro assump_19
  apply And.intro
  cases assump_18
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      cases assump_17
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            cases assump_33
            case inl assump_40 =>
              cases assump_31
              case intro assump_44 assump_45 =>
                have assump_214 : p4 := by
                  exact assump_35
                let assump_55 := assump_23 assump_214
                apply False.elim assump_55
            case inr assump_41 =>
              cases assump_31
              case intro assump_61 assump_62 =>
                exact assump_41
    case inr assump_25 =>
      cases assump_17
      case intro assump_71 assump_72 =>
        cases assump_71
        case intro assump_73 assump_74 =>
          cases assump_73
          case intro assump_75 assump_76 =>
            cases assump_74
            case inl assump_81 =>
              cases assump_72
              case intro assump_85 assump_86 =>
                have assump_215 : p4 := by
                  exact assump_76
                let assump_96 := assump_23 assump_215
                apply False.elim assump_96
            case inr assump_82 =>
              cases assump_72
              case intro assump_102 assump_103 =>
                exact assump_82
  cases assump_18
  case intro assump_110 assump_111 =>
    cases assump_110
    case inl assump_112 =>
      cases assump_17
      case intro assump_118 assump_119 =>
        cases assump_118
        case intro assump_120 assump_121 =>
          cases assump_120
          case intro assump_122 assump_123 =>
            cases assump_121
            case inl assump_128 =>
              cases assump_119
              case intro assump_132 assump_133 =>
                have assump_216 : p4 := by
                  exact assump_123
                let assump_143 := assump_111 assump_216
                apply False.elim assump_143
            case inr assump_129 =>
              cases assump_119
              case intro assump_149 assump_150 =>
                have assump_217 : p4 := by
                  exact assump_123
                let assump_160 := assump_111 assump_217
                apply False.elim assump_160
    case inr assump_113 =>
      cases assump_17
      case intro assump_168 assump_169 =>
        cases assump_168
        case intro assump_170 assump_171 =>
          cases assump_170
          case intro assump_172 assump_173 =>
            cases assump_171
            case inl assump_178 =>
              cases assump_169
              case intro assump_182 assump_183 =>
                have assump_218 : p4 := by
                  exact assump_173
                let assump_193 := assump_111 assump_218
                apply False.elim assump_193
            case inr assump_179 =>
              cases assump_169
              case intro assump_199 assump_200 =>
                have assump_219 : p4 := by
                  exact assump_173
                let assump_210 := assump_111 assump_219
                apply False.elim assump_210


variable (p1 p0 p7 p4 p5 p2 p6 p3 : Prop)
theorem file9_28575 : (((((p2 → False) ∨ (p1 ∨ False)) → ((p1 ∧ p4) → (p1 ∧ p5))) → False) → ((((p5 ∨ False) → (p3 ∧ False)) ∧ ((p0 → False) ∨ (p7 ∨ p7))) → (((p2 → p6) → False) → ((p2 → True) ∨ (p7 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      apply Or.inl
      intro assump_16
      apply True.intro
    case inr assump_11 =>
      cases assump_11
      case inl assump_17 =>
        apply Or.inl
        intro assump_23
        apply True.intro
      case inr assump_18 =>
        apply Or.inl
        intro assump_28
        apply True.intro


variable (p1 p4 p2 p6 p0 p5 p7 p3 : Prop)
theorem file9_29289 : (((((p2 → p4) ∨ (True → False)) ∧ ((p0 → False) ∨ (p7 ∧ True))) → (((p3 ∧ p5) ∨ (True → p4)) → False)) → ((((p1 ∨ False) ∨ (p6 ∨ True)) ∨ ((p3 → p6) → False)) ∨ (((p3 ∧ p5) ∧ (p0 → False)) ∧ ((p3 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p5 p7 p3 p2 p1 p0 : Prop)
theorem file9_29668 : ((((((p2 ∧ p0) ∨ (p7 → p1)) ∧ ((p2 ∨ True) → False)) → False) ∧ ((((False → False) ∧ (p3 ∧ False)) → ((True → False) ∨ (True ∨ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((False → False) ∧ (p3 ∧ False)) → ((True → False) ∨ (True ∨ p5))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p7 p0 p2 p5 p4 p6 p1 p3 : Prop)
theorem file9_30309 : ((((((p4 → p6) ∧ (False → p6)) → False) ∨ (((p7 ∨ False) → False) ∧ ((True → p1) → (p4 ∧ True)))) ∧ ((((p4 → False) → (p2 ∧ p1)) ∧ ((p4 → True) ∨ (p6 ∨ True))) ∧ (((p0 → True) ∧ (p3 ∧ p7)) ∧ ((p5 → p3) → False)))) → False) := by
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
          case inl assump_14 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  have assump_172 : (p5 → p3) := by
                    intro assump_33
                    exact assump_24
                  let assump_32 := assump_19 assump_172
                  apply False.elim assump_32
          case inr assump_15 =>
            cases assump_15
            case inl assump_39 =>
              cases assump_9
              case intro assump_43 assump_44 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  cases assump_46
                  case intro assump_49 assump_50 =>
                    have assump_173 : (p5 → p3) := by
                      intro assump_58
                      exact assump_49
                    let assump_57 := assump_44 assump_173
                    apply False.elim assump_57
            case inr assump_40 =>
              cases assump_9
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  cases assump_69
                  case intro assump_72 assump_73 =>
                    have assump_174 : (p5 → p3) := by
                      intro assump_81
                      exact assump_72
                    let assump_80 := assump_67 assump_174
                    apply False.elim assump_80
    case inr assump_5 =>
      cases assump_5
      case intro assump_87 assump_88 =>
        cases assump_3
        case intro assump_93 assump_94 =>
          cases assump_93
          case intro assump_95 assump_96 =>
            cases assump_96
            case inl assump_99 =>
              cases assump_94
              case intro assump_103 assump_104 =>
                cases assump_103
                case intro assump_105 assump_106 =>
                  cases assump_106
                  case intro assump_109 assump_110 =>
                    have assump_175 : (p5 → p3) := by
                      intro assump_118
                      exact assump_109
                    let assump_117 := assump_104 assump_175
                    apply False.elim assump_117
            case inr assump_100 =>
              cases assump_100
              case inl assump_124 =>
                cases assump_94
                case intro assump_128 assump_129 =>
                  cases assump_128
                  case intro assump_130 assump_131 =>
                    cases assump_131
                    case intro assump_134 assump_135 =>
                      have assump_176 : (p5 → p3) := by
                        intro assump_143
                        exact assump_134
                      let assump_142 := assump_129 assump_176
                      apply False.elim assump_142
              case inr assump_125 =>
                cases assump_94
                case intro assump_151 assump_152 =>
                  cases assump_151
                  case intro assump_153 assump_154 =>
                    cases assump_154
                    case intro assump_157 assump_158 =>
                      have assump_177 : (p5 → p3) := by
                        intro assump_166
                        exact assump_157
                      let assump_165 := assump_152 assump_177
                      apply False.elim assump_165


variable (p7 : Prop)
theorem file9_34372 : (((((True ∨ p7) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((True ∨ p7) → False) → False) := by
    intro assump_5
    have assump_16 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p7 p6 p0 p1 p3 p5 : Prop)
theorem file9_34801 : ((((((p3 ∧ True) → (p6 ∨ p3)) ∨ ((p1 → p7) → False)) ∧ (((p0 ∧ p4) ∨ (p1 → p1)) → False)) ∧ ((((p0 ∨ p6) → False) → ((p0 → p0) ∨ (p4 → False))) → (((p6 ∧ p5) → (True → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_46 : (((p0 ∨ p6) → False) → ((p0 → p0) ∨ (p4 → False))) := by
          intro assump_15
          apply Or.inl
          intro assump_18
          exact assump_18
        let assump_14 := assump_3 assump_46
        have assump_47 : ((p6 ∧ p5) → (True → True)) := by
          intro assump_22
          intro assump_23
          apply True.intro
        let assump_21 := assump_14 assump_47
        apply False.elim assump_21
      case inr assump_7 =>
        have assump_48 : (((p0 ∨ p6) → False) → ((p0 → p0) ∨ (p4 → False))) := by
          intro assump_34
          apply Or.inl
          intro assump_37
          exact assump_37
        let assump_33 := assump_3 assump_48
        have assump_49 : ((p6 ∧ p5) → (True → True)) := by
          intro assump_41
          intro assump_42
          apply True.intro
        let assump_40 := assump_33 assump_49
        apply False.elim assump_40


variable (p6 p2 p3 p5 : Prop)
theorem file9_36144 : ((((((p2 ∨ True) ∧ (p3 → p5)) → ((p6 ∨ True) ∧ (False → False))) ∨ (((p2 → p5) ∧ (False → True)) ∧ ((p2 → False) ∧ (p2 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p2 ∨ True) ∧ (p3 → p5)) → ((p6 ∨ True) ∧ (False → False))) ∨ (((p2 → p5) ∧ (False → True)) ∧ ((p2 → False) ∧ (p2 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        apply True.intro
      case inr assump_9 =>
        apply Or.inr
        apply True.intro
    intro assump_18
    apply False.elim assump_18
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p0 p3 p6 p5 p2 p1 p7 : Prop)
theorem file9_36924 : (((((p4 → False) ∨ (p5 → False)) ∧ ((p2 → False) → False)) → (((p3 ∧ p1) ∧ (p3 ∧ False)) → False)) ∨ ((((False ∧ p2) → (p6 → False)) → False) → (((p5 → p7) → False) ∧ ((False → False) → (p7 ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        apply False.elim assump_12


variable (p1 p3 p5 p2 p4 p0 : Prop)
theorem file9_37441 : (((((True ∨ True) → (True ∧ False)) → False) ∨ (((False ∨ p4) → False) ∧ ((False ∧ p1) → False))) ∨ ((((p0 → False) ∧ (False ∧ p5)) ∧ ((p3 → True) → False)) ∨ (((p4 → False) → False) ∧ ((p2 ∧ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_10 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_10
  let assump_5 := And.right assump_4
  apply False.elim assump_5


variable (p2 p0 : Prop)
theorem file9_37929 : ((((((p0 → True) ∨ (p0 ∧ p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p0 → True) ∨ (p0 ∧ p2)) → False) → False) := by
    intro assump_5
    have assump_17 : ((p0 → True) ∨ (p0 ∧ p2)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p4 p6 p5 p1 p3 p0 : Prop)
theorem file9_38421 : (((((p4 → False) ∧ (False → False)) → False) ∨ (((p1 → p0) → False) → ((p5 ∧ p3) ∧ (p6 → False)))) → ((((False → False) ∨ (False ∧ False)) ∨ ((p0 → False) ∨ (p7 → False))) ∨ (((p0 ∨ p6) ∨ (p6 → False)) ∨ ((False → False) → (p4 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p7 p4 p2 p6 p3 p5 p0 : Prop)
theorem file9_39012 : (((((p7 ∨ p2) ∧ (p3 → False)) → ((p2 ∨ p5) ∧ (False → p4))) ∧ (((True → False) → (p6 → p4)) → False)) → ((((p4 ∨ p6) ∨ (p5 ∨ p3)) → ((p0 ∧ False) ∧ (p6 → False))) ∨ (((p3 ∨ False) → False) → ((p4 ∧ p6) ∨ (p6 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply And.intro
    apply And.intro
    cases assump_8
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        have assump_226 : ((True → False) → (p6 → p4)) := by
          intro assump_17
          intro assump_18
          exact assump_11
        let assump_16 := assump_3 assump_226
        apply False.elim assump_16
      case inr assump_12 =>
        have assump_227 : ((True → False) → (p6 → p4)) := by
          intro assump_30
          intro assump_31
          have assump_228 : True := by
            apply True.intro
          let assump_36 := assump_30 assump_228
          apply False.elim assump_36
        let assump_29 := assump_3 assump_227
        apply False.elim assump_29
    case inr assump_10 =>
      cases assump_10
      case inl assump_43 =>
        have assump_229 : ((True → False) → (p6 → p4)) := by
          intro assump_49
          intro assump_50
          have assump_230 : True := by
            apply True.intro
          let assump_55 := assump_49 assump_230
          apply False.elim assump_55
        let assump_48 := assump_3 assump_229
        apply False.elim assump_48
      case inr assump_44 =>
        have assump_231 : ((True → False) → (p6 → p4)) := by
          intro assump_66
          intro assump_67
          have assump_232 : True := by
            apply True.intro
          let assump_72 := assump_66 assump_232
          apply False.elim assump_72
        let assump_65 := assump_3 assump_231
        apply False.elim assump_65
    cases assump_8
    case inl assump_79 =>
      cases assump_79
      case inl assump_81 =>
        have assump_233 : ((True → False) → (p6 → p4)) := by
          intro assump_87
          intro assump_88
          exact assump_81
        let assump_86 := assump_3 assump_233
        apply False.elim assump_86
      case inr assump_82 =>
        have assump_234 : ((True → False) → (p6 → p4)) := by
          intro assump_100
          intro assump_101
          have assump_235 : True := by
            apply True.intro
          let assump_106 := assump_100 assump_235
          apply False.elim assump_106
        let assump_99 := assump_3 assump_234
        apply False.elim assump_99
    case inr assump_80 =>
      cases assump_80
      case inl assump_113 =>
        have assump_236 : ((True → False) → (p6 → p4)) := by
          intro assump_119
          intro assump_120
          have assump_237 : True := by
            apply True.intro
          let assump_125 := assump_119 assump_237
          apply False.elim assump_125
        let assump_118 := assump_3 assump_236
        apply False.elim assump_118
      case inr assump_114 =>
        have assump_238 : ((True → False) → (p6 → p4)) := by
          intro assump_136
          intro assump_137
          have assump_239 : True := by
            apply True.intro
          let assump_142 := assump_136 assump_239
          apply False.elim assump_142
        let assump_135 := assump_3 assump_238
        apply False.elim assump_135
    intro assump_149
    cases assump_8
    case inl assump_152 =>
      cases assump_152
      case inl assump_154 =>
        have assump_240 : ((True → False) → (p6 → p4)) := by
          intro assump_161
          intro assump_162
          exact assump_154
        let assump_160 := assump_3 assump_240
        apply False.elim assump_160
      case inr assump_155 =>
        have assump_241 : ((True → False) → (p6 → p4)) := by
          intro assump_175
          intro assump_176
          have assump_242 : True := by
            apply True.intro
          let assump_181 := assump_175 assump_242
          apply False.elim assump_181
        let assump_174 := assump_3 assump_241
        apply False.elim assump_174
    case inr assump_153 =>
      cases assump_153
      case inl assump_188 =>
        have assump_243 : ((True → False) → (p6 → p4)) := by
          intro assump_195
          intro assump_196
          have assump_244 : True := by
            apply True.intro
          let assump_201 := assump_195 assump_244
          apply False.elim assump_201
        let assump_194 := assump_3 assump_243
        apply False.elim assump_194
      case inr assump_189 =>
        have assump_245 : ((True → False) → (p6 → p4)) := by
          intro assump_213
          intro assump_214
          have assump_246 : True := by
            apply True.intro
          let assump_219 := assump_213 assump_246
          apply False.elim assump_219
        let assump_212 := assump_3 assump_245
        apply False.elim assump_212


variable (p5 p2 p1 p6 p4 p7 p3 : Prop)
theorem file9_43969 : (((((False ∧ p6) ∧ (p7 ∧ p6)) → False) ∧ (((p2 ∨ p7) → (p2 → p2)) ∧ ((p5 → p5) ∧ (p5 ∧ p4)))) → ((((p5 → p4) → False) → ((p4 → p1) ∧ (p6 → p3))) ∧ (((True → False) → False) ∨ ((False → False) → False)))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_5
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          have assump_104 : (p5 → p4) := by
            intro assump_37
            exact assump_25
          let assump_36 := assump_6 assump_104
          apply False.elim assump_36
  intro assump_43
  cases assump_5
  case intro assump_48 assump_49 =>
    cases assump_49
    case intro assump_52 assump_53 =>
      cases assump_53
      case intro assump_56 assump_57 =>
        cases assump_57
        case intro assump_60 assump_61 =>
          have assump_105 : (p5 → p4) := by
            intro assump_73
            exact assump_61
          let assump_72 := assump_6 assump_105
          apply False.elim assump_72
  cases assump_5
  case intro assump_79 assump_80 =>
    cases assump_80
    case intro assump_83 assump_84 =>
      cases assump_84
      case intro assump_87 assump_88 =>
        cases assump_88
        case intro assump_91 assump_92 =>
          apply Or.inl
          intro assump_97
          have assump_106 : True := by
            apply True.intro
          let assump_100 := assump_97 assump_106
          apply False.elim assump_100


variable (p3 p7 p1 p5 p0 : Prop)
theorem file9_45630 : (((((True ∨ p7) → (True → False)) → False) ∧ (((False → False) → False) → False)) ∨ ((((True ∨ True) → False) → False) ∧ (((p5 ∨ p7) ∧ (p1 → False)) → ((p0 ∧ p3) ∧ (True → False))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  have assump_19 : (True ∨ p7) := by
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_19
  have assump_20 : True := by
    apply True.intro
  let assump_5 := assump_4 assump_20
  apply False.elim assump_5
  intro assump_9
  have assump_21 : (False → False) := by
    intro assump_13
    apply False.elim assump_13
  let assump_12 := assump_9 assump_21
  apply False.elim assump_12


variable (p6 p7 p2 p0 p5 p4 p1 p3 : Prop)
theorem file9_46339 : (((((p1 → False) ∨ (p4 → False)) → False) ∧ (((p6 ∨ True) ∨ (p7 ∧ p2)) → False)) → ((((p6 ∨ p3) ∨ (p2 → p5)) ∧ ((p0 ∧ p6) ∨ (p0 → p7))) → False)) := by
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_4
            case intro assump_22 assump_23 =>
              have assump_108 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
                apply Or.inl
                apply Or.inl
                exact assump_17
              let assump_28 := assump_23 assump_108
              apply False.elim assump_28
        case inr assump_15 =>
          cases assump_4
          case intro assump_34 assump_35 =>
            have assump_109 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              exact assump_10
            let assump_40 := assump_35 assump_109
            apply False.elim assump_40
      case inr assump_11 =>
        cases assump_7
        case inl assump_46 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_4
            case intro assump_54 assump_55 =>
              have assump_110 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
                apply Or.inl
                apply Or.inl
                exact assump_49
              let assump_60 := assump_55 assump_110
              apply False.elim assump_60
        case inr assump_47 =>
          cases assump_4
          case intro assump_66 assump_67 =>
            have assump_111 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_72 := assump_67 assump_111
            apply False.elim assump_72
    case inr assump_9 =>
      cases assump_7
      case inl assump_78 =>
        cases assump_78
        case intro assump_80 assump_81 =>
          cases assump_4
          case intro assump_86 assump_87 =>
            have assump_112 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
              apply Or.inl
              apply Or.inl
              exact assump_81
            let assump_92 := assump_87 assump_112
            apply False.elim assump_92
      case inr assump_79 =>
        cases assump_4
        case intro assump_98 assump_99 =>
          have assump_113 : ((p6 ∨ True) ∨ (p7 ∧ p2)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_104 := assump_99 assump_113
          apply False.elim assump_104


variable (p1 p6 p7 p4 p5 p2 : Prop)
theorem file9_49075 : (((((p5 ∧ p6) → False) ∧ ((p6 ∧ False) ∨ (p1 ∧ False))) → False) ∨ ((((p5 → p7) ∨ (p1 ∧ p6)) ∧ ((p2 → p7) → (p1 ∨ p1))) ∨ (((p1 ∨ p6) ∧ (False ∨ p1)) ∨ ((p4 → False) → False)))) := by
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
        apply False.elim assump_15


variable (p4 p7 p0 p5 : Prop)
theorem file9_49654 : ((((((False ∨ p5) → (False ∨ p4)) ∨ ((p0 ∧ True) ∧ (True → True))) ∧ (((p7 → False) ∨ (False ∨ p5)) ∧ ((p5 → False) ∧ (True → False)))) ∨ ((((p5 → False) → False) ∨ ((False ∧ True) → False)) ∧ (((True → False) → False) → False))) → False) := by
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
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              have assump_118 : True := by
                apply True.intro
              let assump_22 := assump_17 assump_118
              apply False.elim assump_22
          case inr assump_13 =>
            cases assump_13
            case inl assump_26 =>
              apply False.elim assump_26
            case inr assump_27 =>
              cases assump_11
              case intro assump_32 assump_33 =>
                have assump_119 : True := by
                  apply True.intro
                let assump_38 := assump_33 assump_119
                apply False.elim assump_38
      case inr assump_7 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_42
          case intro assump_44 assump_45 =>
            cases assump_5
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                cases assump_53
                case intro assump_58 assump_59 =>
                  have assump_120 : True := by
                    apply True.intro
                  let assump_64 := assump_59 assump_120
                  apply False.elim assump_64
              case inr assump_55 =>
                cases assump_55
                case inl assump_68 =>
                  apply False.elim assump_68
                case inr assump_69 =>
                  cases assump_53
                  case intro assump_74 assump_75 =>
                    have assump_121 : True := by
                      apply True.intro
                    let assump_80 := assump_75 assump_121
                    apply False.elim assump_80
  case inr assump_3 =>
    cases assump_3
    case intro assump_84 assump_85 =>
      cases assump_84
      case inl assump_86 =>
        have assump_122 : ((True → False) → False) := by
          intro assump_93
          have assump_123 : True := by
            apply True.intro
          let assump_96 := assump_93 assump_123
          apply False.elim assump_96
        let assump_92 := assump_85 assump_122
        apply False.elim assump_92
      case inr assump_87 =>
        have assump_124 : ((True → False) → False) := by
          intro assump_108
          have assump_125 : True := by
            apply True.intro
          let assump_111 := assump_108 assump_125
          apply False.elim assump_111
        let assump_107 := assump_85 assump_124
        apply False.elim assump_107


variable (p4 p2 p7 p6 p1 p3 p5 : Prop)
theorem file9_52746 : (((((p4 ∨ p1) → (p2 → False)) → False) ∧ (((p3 → False) → False) → ((p6 → p4) ∧ (p5 ∧ p7)))) → ((((p7 ∧ False) ∧ (p3 ∧ p3)) → ((False → False) ∨ (p4 → p1))) ∨ (((False ∨ p5) ∧ (True ∨ p3)) → ((p1 ∧ p3) → False)))) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    apply Or.inl
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        apply False.elim assump_24


variable (p6 p0 p2 p1 p7 p4 : Prop)
theorem file9_53290 : ((((((p6 ∧ p4) → (p7 ∧ p2)) → ((p6 ∨ True) → False)) ∨ (((True ∨ p6) ∧ (p6 ∨ p0)) → False)) ∧ ((((True → False) → (p1 ∨ p6)) ∨ ((p2 → p0) ∨ (p6 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : (((True → False) → (p1 ∨ p6)) ∨ ((p2 → p0) ∨ (p6 → False))) := by
        apply Or.inl
        intro assump_11
        have assump_37 : True := by
          apply True.intro
        let assump_14 := assump_11 assump_37
        apply False.elim assump_14
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_38 : (((True → False) → (p1 ∨ p6)) ∨ ((p2 → p0) ∨ (p6 → False))) := by
        apply Or.inl
        intro assump_26
        have assump_39 : True := by
          apply True.intro
        let assump_29 := assump_26 assump_39
        apply False.elim assump_29
      let assump_25 := assump_3 assump_38
      apply False.elim assump_25


variable (p5 p0 p1 p3 p6 p4 p2 : Prop)
theorem file9_54374 : (((((p6 ∨ True) ∨ (p3 → False)) → False) → (((True ∧ p3) ∧ (p6 → p2)) ∨ ((p2 → False) ∨ (False → p4)))) ∨ ((((p6 → False) → (p3 ∨ False)) → ((p0 ∨ False) ∧ (p3 ∨ p5))) ∨ (((True → False) ∨ (False → False)) ∨ ((p6 → False) ∨ (p2 ∨ p1))))) := by
  apply Or.inl
  intro assump_5
  apply Or.inr
  apply Or.inl
  intro assump_8
  have assump_16 : ((p6 ∨ True) ∨ (p3 → False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_12 := assump_5 assump_16
  apply False.elim assump_12


variable (p4 p6 p1 : Prop)
theorem file9_54924 : (((((False ∨ p4) → (False → False)) ∨ ((p4 → p4) ∨ (p1 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_12 : (((False ∨ p4) → (False → False)) ∨ ((p4 → p4) ∨ (p1 ∧ p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p6 p1 p4 p5 p7 p0 p3 : Prop)
theorem file9_55330 : (((((True ∨ p4) → (True ∨ p5)) → False) → (((False → True) ∧ (False → False)) ∧ ((p2 ∧ p2) ∨ (p6 ∧ False)))) ∨ ((((p1 ∨ p3) ∧ (p3 → False)) ∧ ((p4 ∧ True) ∨ (p3 ∨ p2))) ∨ (((p0 ∧ p5) ∧ (p7 ∨ True)) ∨ ((True ∧ True) ∨ (p5 ∧ p5))))) := by
  apply Or.inl
  intro assump_29
  apply And.intro
  apply And.intro
  intro assump_30
  apply True.intro
  intro assump_31
  apply False.elim assump_31
  have assump_47 : ((True ∨ p4) → (True ∨ p5)) := by
    intro assump_37
    cases assump_37
    case inl assump_38 =>
      apply Or.inl
      apply True.intro
    case inr assump_39 =>
      apply Or.inl
      apply True.intro
  let assump_36 := assump_29 assump_47
  apply False.elim assump_36


variable (p0 p2 p6 p1 p4 p5 p3 p7 : Prop)
theorem file9_56083 : (((((True ∧ p7) ∨ (p4 → p3)) ∧ ((p3 ∨ p1) → (p5 → p0))) ∧ (((False → False) ∧ (p7 ∧ False)) ∧ ((p1 ∨ p2) → (p6 → p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case intro assump_22 assump_23 =>
                apply False.elim assump_23
      case inr assump_7 =>
        cases assump_3
        case intro assump_32 assump_33 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            cases assump_35
            case intro assump_38 assump_39 =>
              apply False.elim assump_39


variable (p3 p0 p7 p1 p6 p2 p5 p4 : Prop)
theorem file9_57059 : ((((((p2 → False) → (p2 → p5)) ∨ ((p7 ∧ p6) → (p1 → False))) ∨ (((p3 → p4) → (p6 → False)) ∧ ((False → p0) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → False) → (p2 → p5)) ∨ ((p7 ∧ p6) → (p1 → False))) ∨ (((p3 → p4) → (p6 → False)) ∧ ((False → p0) ∧ (True → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : p2 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p1 p0 p7 : Prop)
theorem file9_57690 : ((((((p7 → False) → (False → True)) ∧ ((p7 ∨ p0) ∧ (p5 ∨ p7))) ∨ (((True ∨ p5) → (False ∧ p1)) → ((True → False) ∨ (False ∨ p7)))) → False) → False) := by
  intro assump_9
  have assump_29 : ((((p7 → False) → (False → True)) ∧ ((p7 ∨ p0) ∧ (p5 ∨ p7))) ∨ (((True ∨ p5) → (False ∧ p1)) → ((True → False) ∨ (False ∨ p7)))) := by
    apply Or.inr
    intro assump_15
    apply Or.inl
    intro assump_18
    have assump_30 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_21 := assump_15 assump_30
    let assump_22 := And.left assump_21
    apply False.elim assump_22
  let assump_12 := assump_9 assump_29
  apply False.elim assump_12


variable (p4 p1 p7 p2 p5 p0 p6 : Prop)
theorem file9_58413 : (((((p0 ∧ p7) ∧ (False ∨ p4)) ∧ ((p4 → p0) ∧ (True ∨ p4))) → (((p7 → False) → False) ∧ ((p6 ∨ p6) → (p7 → p5)))) → ((((p2 → False) ∨ (p5 ∨ p5)) → False) → (((False ∧ p1) → False) ∨ ((p4 ∨ p0) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p7 p5 p0 p3 p2 p1 p4 : Prop)
theorem file9_58843 : (((((p4 → p3) ∨ (False → False)) ∨ ((p0 ∨ True) ∧ (p1 → p5))) ∨ (((p4 ∨ p7) ∨ (True ∨ p2)) ∨ ((p1 ∧ p7) ∧ (p5 ∨ p7)))) → ((((False ∧ p3) ∧ (p4 ∧ True)) → ((p4 → p7) → False)) ∨ (((p5 ∧ p5) → (p1 ∧ p0)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_10
        intro assump_11
        cases assump_10
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
      case inr assump_7 =>
        apply Or.inl
        intro assump_22
        intro assump_23
        cases assump_22
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
    case inr assump_5 =>
      cases assump_5
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          apply Or.inl
          intro assump_40
          intro assump_41
          cases assump_40
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply False.elim assump_46
        case inr assump_35 =>
          apply Or.inl
          intro assump_54
          intro assump_55
          cases assump_54
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              apply False.elim assump_60
  case inr assump_3 =>
    cases assump_3
    case inl assump_64 =>
      cases assump_64
      case inl assump_66 =>
        cases assump_66
        case inl assump_68 =>
          apply Or.inl
          intro assump_72
          intro assump_73
          cases assump_72
          case intro assump_76 assump_77 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              apply False.elim assump_78
        case inr assump_69 =>
          apply Or.inl
          intro assump_84
          intro assump_85
          cases assump_84
          case intro assump_88 assump_89 =>
            cases assump_88
            case intro assump_90 assump_91 =>
              apply False.elim assump_90
      case inr assump_67 =>
        cases assump_67
        case inl assump_94 =>
          apply Or.inl
          intro assump_98
          intro assump_99
          cases assump_98
          case intro assump_102 assump_103 =>
            cases assump_102
            case intro assump_104 assump_105 =>
              apply False.elim assump_104
        case inr assump_95 =>
          apply Or.inl
          intro assump_110
          intro assump_111
          cases assump_110
          case intro assump_114 assump_115 =>
            cases assump_114
            case intro assump_116 assump_117 =>
              apply False.elim assump_116
    case inr assump_65 =>
      cases assump_65
      case intro assump_120 assump_121 =>
        cases assump_120
        case intro assump_122 assump_123 =>
          cases assump_121
          case inl assump_128 =>
            apply Or.inl
            intro assump_132
            intro assump_133
            cases assump_132
            case intro assump_136 assump_137 =>
              cases assump_136
              case intro assump_138 assump_139 =>
                apply False.elim assump_138
          case inr assump_129 =>
            apply Or.inl
            intro assump_144
            intro assump_145
            cases assump_144
            case intro assump_148 assump_149 =>
              cases assump_148
              case intro assump_150 assump_151 =>
                apply False.elim assump_150


variable (p3 p5 p7 p6 p1 p0 p4 p2 : Prop)
theorem file9_62673 : ((((((p1 → p3) → (p0 → True)) → ((p2 → False) ∧ (p5 → p0))) ∨ (((p1 → True) ∨ (True → False)) ∧ ((p2 → p1) ∨ (p5 → False)))) ∧ ((((p0 ∨ False) → (p4 → False)) ∨ ((p0 ∨ p2) → (p7 ∨ p1))) ∧ (((p3 → True) ∨ (p1 ∧ p6)) → ((p2 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_158 : ((p3 → True) ∨ (p1 ∧ p6)) := by
            apply Or.inl
            intro assump_17
            apply True.intro
          let assump_16 := assump_9 assump_158
          have assump_159 : (p2 → True) := by
            intro assump_19
            apply True.intro
          let assump_18 := assump_16 assump_159
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_160 : ((p3 → True) ∨ (p1 ∧ p6)) := by
            apply Or.inl
            intro assump_28
            apply True.intro
          let assump_27 := assump_9 assump_160
          have assump_161 : (p2 → True) := by
            intro assump_30
            apply True.intro
          let assump_29 := assump_27 assump_161
          apply False.elim assump_29
    case inr assump_5 =>
      cases assump_5
      case intro assump_34 assump_35 =>
        cases assump_34
        case inl assump_36 =>
          cases assump_35
          case inl assump_40 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              cases assump_44
              case inl assump_46 =>
                have assump_162 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_53
                  apply True.intro
                let assump_52 := assump_45 assump_162
                have assump_163 : (p2 → True) := by
                  intro assump_55
                  apply True.intro
                let assump_54 := assump_52 assump_163
                apply False.elim assump_54
              case inr assump_47 =>
                have assump_164 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_64
                  apply True.intro
                let assump_63 := assump_45 assump_164
                have assump_165 : (p2 → True) := by
                  intro assump_66
                  apply True.intro
                let assump_65 := assump_63 assump_165
                apply False.elim assump_65
          case inr assump_41 =>
            cases assump_3
            case intro assump_72 assump_73 =>
              cases assump_72
              case inl assump_74 =>
                have assump_166 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_81
                  apply True.intro
                let assump_80 := assump_73 assump_166
                have assump_167 : (p2 → True) := by
                  intro assump_83
                  apply True.intro
                let assump_82 := assump_80 assump_167
                apply False.elim assump_82
              case inr assump_75 =>
                have assump_168 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_92
                  apply True.intro
                let assump_91 := assump_73 assump_168
                have assump_169 : (p2 → True) := by
                  intro assump_94
                  apply True.intro
                let assump_93 := assump_91 assump_169
                apply False.elim assump_93
        case inr assump_37 =>
          cases assump_35
          case inl assump_100 =>
            cases assump_3
            case intro assump_104 assump_105 =>
              cases assump_104
              case inl assump_106 =>
                have assump_170 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_113
                  apply True.intro
                let assump_112 := assump_105 assump_170
                have assump_171 : (p2 → True) := by
                  intro assump_115
                  apply True.intro
                let assump_114 := assump_112 assump_171
                apply False.elim assump_114
              case inr assump_107 =>
                have assump_172 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_124
                  apply True.intro
                let assump_123 := assump_105 assump_172
                have assump_173 : (p2 → True) := by
                  intro assump_126
                  apply True.intro
                let assump_125 := assump_123 assump_173
                apply False.elim assump_125
          case inr assump_101 =>
            cases assump_3
            case intro assump_132 assump_133 =>
              cases assump_132
              case inl assump_134 =>
                have assump_174 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_141
                  apply True.intro
                let assump_140 := assump_133 assump_174
                have assump_175 : (p2 → True) := by
                  intro assump_143
                  apply True.intro
                let assump_142 := assump_140 assump_175
                apply False.elim assump_142
              case inr assump_135 =>
                have assump_176 : ((p3 → True) ∨ (p1 ∧ p6)) := by
                  apply Or.inl
                  intro assump_152
                  apply True.intro
                let assump_151 := assump_133 assump_176
                have assump_177 : (p2 → True) := by
                  intro assump_154
                  apply True.intro
                let assump_153 := assump_151 assump_177
                apply False.elim assump_153


variable (p3 p4 p2 p5 p0 p7 p6 : Prop)
theorem file9_68595 : ((((((False → p2) ∧ (p4 → False)) ∧ ((p3 → False) → (p0 → False))) ∨ (((p5 ∨ p4) ∨ (p0 → p4)) ∨ ((p0 ∧ p7) ∨ (p5 ∧ p3)))) ∧ ((((False → False) → (p7 → False)) ∨ ((True → False) → (p7 ∧ p6))) ∧ (((p0 → False) → (True ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_198 : ((p0 → False) → (True ∨ p0)) := by
                intro assump_25
                apply Or.inl
                apply True.intro
              let assump_24 := assump_17 assump_198
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_199 : ((p0 → False) → (True ∨ p0)) := by
                intro assump_36
                apply Or.inl
                apply True.intro
              let assump_35 := assump_17 assump_199
              apply False.elim assump_35
    case inr assump_5 =>
      cases assump_5
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          cases assump_44
          case inl assump_46 =>
            cases assump_3
            case intro assump_50 assump_51 =>
              cases assump_50
              case inl assump_52 =>
                have assump_200 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_59
                  apply Or.inl
                  apply True.intro
                let assump_58 := assump_51 assump_200
                apply False.elim assump_58
              case inr assump_53 =>
                have assump_201 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_70
                  apply Or.inl
                  apply True.intro
                let assump_69 := assump_51 assump_201
                apply False.elim assump_69
          case inr assump_47 =>
            cases assump_3
            case intro assump_78 assump_79 =>
              cases assump_78
              case inl assump_80 =>
                have assump_202 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_87
                  apply Or.inl
                  apply True.intro
                let assump_86 := assump_79 assump_202
                apply False.elim assump_86
              case inr assump_81 =>
                have assump_203 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_98
                  apply Or.inl
                  apply True.intro
                let assump_97 := assump_79 assump_203
                apply False.elim assump_97
        case inr assump_45 =>
          cases assump_3
          case intro assump_106 assump_107 =>
            cases assump_106
            case inl assump_108 =>
              have assump_204 : ((p0 → False) → (True ∨ p0)) := by
                intro assump_115
                apply Or.inl
                apply True.intro
              let assump_114 := assump_107 assump_204
              apply False.elim assump_114
            case inr assump_109 =>
              have assump_205 : ((p0 → False) → (True ∨ p0)) := by
                intro assump_126
                apply Or.inl
                apply True.intro
              let assump_125 := assump_107 assump_205
              apply False.elim assump_125
      case inr assump_43 =>
        cases assump_43
        case inl assump_132 =>
          cases assump_132
          case intro assump_134 assump_135 =>
            cases assump_3
            case intro assump_140 assump_141 =>
              cases assump_140
              case inl assump_142 =>
                have assump_206 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_149
                  apply Or.inl
                  apply True.intro
                let assump_148 := assump_141 assump_206
                apply False.elim assump_148
              case inr assump_143 =>
                have assump_207 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_160
                  apply Or.inl
                  apply True.intro
                let assump_159 := assump_141 assump_207
                apply False.elim assump_159
        case inr assump_133 =>
          cases assump_133
          case intro assump_166 assump_167 =>
            cases assump_3
            case intro assump_172 assump_173 =>
              cases assump_172
              case inl assump_174 =>
                have assump_208 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_181
                  apply Or.inl
                  apply True.intro
                let assump_180 := assump_173 assump_208
                apply False.elim assump_180
              case inr assump_175 =>
                have assump_209 : ((p0 → False) → (True ∨ p0)) := by
                  intro assump_192
                  apply Or.inl
                  apply True.intro
                let assump_191 := assump_173 assump_209
                apply False.elim assump_191


variable (p7 p5 p4 p6 p2 p0 p3 p1 : Prop)
theorem file9_73865 : ((((((p3 ∨ p6) ∧ (p5 ∨ p0)) ∨ ((p2 → p2) ∨ (p3 ∨ p7))) ∨ (((p4 → p1) → (p0 ∧ p7)) ∨ ((False ∨ p4) ∧ (True ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 ∨ p6) ∧ (p5 ∨ p0)) ∨ ((p2 → p2) ∨ (p3 ∨ p7))) ∨ (((p4 → p1) → (p0 ∧ p7)) ∨ ((False ∨ p4) ∧ (True ∨ False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p7 p0 p5 p2 p3 p4 : Prop)
theorem file9_74382 : (((((p7 → False) → (p2 → p3)) ∧ ((False ∨ True) → False)) ∧ (((p4 ∧ p0) → False) ∨ ((p3 ∧ p6) ∧ (p5 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_36 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_15 := assump_5 assump_36
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            have assump_37 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_32 := assump_5 assump_37
            apply False.elim assump_32


variable (p3 p5 p0 p1 p6 p2 p7 p4 : Prop)
theorem file9_75281 : (((((p5 → False) ∨ (True ∧ False)) ∧ ((True → p5) → False)) → (((p5 ∧ p5) → (p5 → p1)) → ((p4 ∨ p4) → (p5 → False)))) ∨ ((((p5 ∨ p6) → False) ∧ ((p2 ∨ p0) ∨ (p7 ∧ p6))) → (((p7 ∨ p4) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_1
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        have assump_59 : (True → p5) := by
          intro assump_22
          exact assump_4
        let assump_21 := assump_14 assump_59
        apply False.elim assump_21
      case inr assump_16 =>
        cases assump_16
        case intro assump_28 assump_29 =>
          apply False.elim assump_29
  case inr assump_8 =>
    cases assump_1
    case intro assump_38 assump_39 =>
      cases assump_38
      case inl assump_40 =>
        have assump_60 : (True → p5) := by
          intro assump_47
          exact assump_4
        let assump_46 := assump_39 assump_60
        apply False.elim assump_46
      case inr assump_41 =>
        cases assump_41
        case intro assump_53 assump_54 =>
          apply False.elim assump_54


variable (p0 p3 p6 p5 p7 p4 p1 : Prop)
theorem file9_76530 : (((((p0 → p3) ∧ (p6 ∧ False)) → ((False ∨ p0) ∧ (False ∨ p0))) ∨ (((p7 → p4) → False) ∧ ((p0 ∧ p1) ∨ (p7 ∧ p7)))) → ((((True ∨ p3) ∨ (p7 → False)) ∨ ((p5 ∨ p0) ∨ (p7 → False))) ∨ (((p7 → p7) → False) ∨ ((p0 ∨ False) → False)))) := by
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_17 =>
        cases assump_17
        case intro assump_24 assump_25 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro


variable (p1 p3 p6 p4 p5 p7 p0 p2 : Prop)
theorem file9_77504 : (((((p6 ∨ True) ∨ (p0 → False)) → False) → (((p3 → False) → False) ∧ ((p6 ∨ p7) ∧ (p5 → False)))) → ((((p2 ∧ p2) ∧ (True → p0)) → ((p6 → False) ∨ (p2 → p7))) → (((p1 ∧ p7) → False) → ((p1 ∧ p4) → (False → p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p7 p6 p5 : Prop)
theorem file9_77887 : ((((((p5 ∧ p6) → (p7 ∨ True)) → False) → False) → False) → False) := by
  intro assump_64
  have assump_85 : ((((p5 ∧ p6) → (p7 ∨ True)) → False) → False) := by
    intro assump_68
    have assump_86 : ((p5 ∧ p6) → (p7 ∨ True)) := by
      intro assump_72
      cases assump_72
      case intro assump_73 assump_74 =>
        apply Or.inr
        apply True.intro
    let assump_71 := assump_68 assump_86
    apply False.elim assump_71
  let assump_67 := assump_64 assump_85
  apply False.elim assump_67


variable (p4 p7 p6 p1 p2 p0 p3 : Prop)
theorem file9_78454 : (((((p2 ∧ True) ∧ (p4 ∨ p6)) ∧ ((True → False) ∧ (p3 ∨ True))) ∧ (((p0 → False) → (p7 → False)) ∧ ((p0 ∨ p2) ∧ (p3 → False)))) → ((((p1 ∧ p1) → (True ∧ p2)) ∨ ((p1 ∧ False) → (p3 ∨ False))) ∨ (((p2 → p7) → False) → False))) := by
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
          case inl assump_14 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_27
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case inl assump_32 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_38
                      apply And.intro
                      apply True.intro
                      cases assump_38
                      case intro assump_39 assump_40 =>
                        exact assump_8
                    case inr assump_33 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_49
                      apply And.intro
                      apply True.intro
                      cases assump_49
                      case intro assump_50 assump_51 =>
                        exact assump_33
              case inr assump_23 =>
                cases assump_3
                case intro assump_58 assump_59 =>
                  cases assump_59
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case inl assump_64 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_70
                      apply And.intro
                      apply True.intro
                      cases assump_70
                      case intro assump_71 assump_72 =>
                        exact assump_8
                    case inr assump_65 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_81
                      apply And.intro
                      apply True.intro
                      cases assump_81
                      case intro assump_82 assump_83 =>
                        exact assump_65
          case inr assump_15 =>
            cases assump_5
            case intro assump_90 assump_91 =>
              cases assump_91
              case inl assump_94 =>
                cases assump_3
                case intro assump_98 assump_99 =>
                  cases assump_99
                  case intro assump_102 assump_103 =>
                    cases assump_102
                    case inl assump_104 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_110
                      apply And.intro
                      apply True.intro
                      cases assump_110
                      case intro assump_111 assump_112 =>
                        exact assump_8
                    case inr assump_105 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_121
                      apply And.intro
                      apply True.intro
                      cases assump_121
                      case intro assump_122 assump_123 =>
                        exact assump_105
              case inr assump_95 =>
                cases assump_3
                case intro assump_130 assump_131 =>
                  cases assump_131
                  case intro assump_134 assump_135 =>
                    cases assump_134
                    case inl assump_136 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_142
                      apply And.intro
                      apply True.intro
                      cases assump_142
                      case intro assump_143 assump_144 =>
                        exact assump_8
                    case inr assump_137 =>
                      apply Or.inl
                      apply Or.inl
                      intro assump_153
                      apply And.intro
                      apply True.intro
                      cases assump_153
                      case intro assump_154 assump_155 =>
                        exact assump_137


variable (p3 p7 p2 p0 : Prop)
theorem file9_83149 : ((((((False → p3) ∨ (p3 ∧ p0)) ∨ ((False ∧ p7) ∨ (p7 → False))) ∨ (((p7 ∧ True) ∨ (p2 → p7)) → ((p2 → False) ∧ (p7 ∧ False)))) → False) → False) := by
  intro assump_23
  have assump_33 : ((((False → p3) ∨ (p3 ∧ p0)) ∨ ((False ∧ p7) ∨ (p7 → False))) ∨ (((p7 ∧ True) ∨ (p2 → p7)) → ((p2 → False) ∧ (p7 ∧ False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_27
    apply False.elim assump_27
  let assump_26 := assump_23 assump_33
  apply False.elim assump_26


variable (p1 p0 p2 p3 p4 p5 p7 : Prop)
theorem file9_83701 : ((((((p0 → p2) ∧ (p4 → p0)) → False) ∧ (((p4 ∨ p2) → (p7 → p1)) → ((p3 → p5) → (p2 ∨ p3)))) ∧ ((((p0 ∨ p5) ∧ (True ∧ p7)) → False) ∧ (((p7 ∨ True) ∨ (True ∨ p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_20 : ((p7 ∨ True) ∨ (True ∨ p1)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p4 p5 p2 : Prop)
theorem file9_84336 : ((((((False → p2) ∨ (p5 → p4)) → False) → False) → False) → False) := by
  intro assump_5
  have assump_22 : ((((False → p2) ∨ (p5 → p4)) → False) → False) := by
    intro assump_9
    have assump_23 : ((False → p2) ∨ (p5 → p4)) := by
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_9 assump_23
    apply False.elim assump_12
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p7 p6 p2 p0 p3 p5 p1 : Prop)
theorem file9_84844 : (((((p5 → p1) → (p0 ∨ p2)) → ((False → False) ∨ (p6 → False))) ∨ (((p7 → p1) → False) ∧ ((p3 → False) ∧ (p5 ∧ p5)))) ∨ ((((p1 ∨ p5) → False) ∧ ((True ∨ True) → (p7 → False))) ∨ (((p5 ∧ True) → (False ∨ p0)) → ((p5 ∨ p0) ∨ (p2 → p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p4 p1 p5 p0 p7 p6 p2 : Prop)
theorem file9_85256 : (((((p2 ∧ p1) ∧ (False ∧ p4)) → ((p7 → False) ∧ (p0 → False))) ∨ (((p5 → False) → False) → False)) ∨ ((((True ∧ p4) ∨ (p0 → False)) → ((True → p1) ∧ (p2 ∧ p6))) → (((p4 ∨ p1) → (p6 ∧ p4)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
  intro assump_17
  cases assump_1
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_21
      case intro assump_28 assump_29 =>
        apply False.elim assump_28


variable (p7 p1 p6 p3 p0 p2 p5 : Prop)
theorem file9_86034 : (((((p2 ∨ p7) ∧ (p6 → p7)) ∨ ((p0 → p3) → (p0 → p0))) → False) → ((((p5 ∨ p2) → False) ∨ ((p2 → False) → (p5 ∧ p1))) → (((True → False) ∧ (p7 ∧ p5)) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_6
      case inl assump_18 =>
        have assump_42 : (((p2 ∨ p7) ∧ (p6 → p7)) ∨ ((p0 → p3) → (p0 → p0))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_12
          intro assump_25
          exact assump_12
        let assump_24 := assump_5 assump_42
        apply False.elim assump_24
      case inr assump_19 =>
        have assump_43 : (((p2 ∨ p7) ∧ (p6 → p7)) ∨ ((p0 → p3) → (p0 → p0))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_12
          intro assump_36
          exact assump_12
        let assump_35 := assump_5 assump_43
        apply False.elim assump_35


variable (p4 p6 p1 p0 p7 p3 : Prop)
theorem file9_87120 : (((((p1 ∨ p4) → (True → False)) ∧ ((p7 ∨ True) ∧ (p6 → p1))) ∧ (((False → False) → (p7 → False)) ∧ ((True ∨ False) → False))) → ((((p4 ∨ p0) ∨ (True → False)) → False) → (((False → False) → False) ∧ ((p7 ∧ p7) → (True → p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            have assump_96 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_28 := assump_23 assump_96
            apply False.elim assump_28
        case inr assump_17 =>
          cases assump_9
          case intro assump_36 assump_37 =>
            have assump_97 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_42 := assump_37 assump_97
            apply False.elim assump_42
  intro assump_46
  intro assump_47
  cases assump_46
  case intro assump_50 assump_51 =>
    cases assump_1
    case intro assump_58 assump_59 =>
      cases assump_58
      case intro assump_60 assump_61 =>
        cases assump_61
        case intro assump_64 assump_65 =>
          cases assump_64
          case inl assump_66 =>
            cases assump_59
            case intro assump_72 assump_73 =>
              have assump_98 : (True ∨ False) := by
                apply Or.inl
                apply True.intro
              let assump_78 := assump_73 assump_98
              apply False.elim assump_78
          case inr assump_67 =>
            cases assump_59
            case intro assump_86 assump_87 =>
              have assump_99 : (True ∨ False) := by
                apply Or.inl
                apply True.intro
              let assump_92 := assump_87 assump_99
              apply False.elim assump_92


variable (p0 p5 p4 p6 : Prop)
theorem file9_89186 : (((((p0 → False) → (p6 → p0)) ∧ ((p4 ∨ True) ∨ (p5 → p5))) ∧ (((p4 → True) → False) ∨ ((False → False) → False))) → False) := by
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
          case inl assump_14 =>
            have assump_72 : (p4 → True) := by
              intro assump_19
              apply True.intro
            let assump_18 := assump_14 assump_72
            apply False.elim assump_18
          case inr assump_15 =>
            have assump_73 : (False → False) := by
              intro assump_26
              apply False.elim assump_26
            let assump_25 := assump_15 assump_73
            apply False.elim assump_25
        case inr assump_11 =>
          cases assump_3
          case inl assump_34 =>
            have assump_74 : (p4 → True) := by
              intro assump_39
              apply True.intro
            let assump_38 := assump_34 assump_74
            apply False.elim assump_38
          case inr assump_35 =>
            have assump_75 : (False → False) := by
              intro assump_46
              apply False.elim assump_46
            let assump_45 := assump_35 assump_75
            apply False.elim assump_45
      case inr assump_9 =>
        cases assump_3
        case inl assump_54 =>
          have assump_76 : (p4 → True) := by
            intro assump_59
            apply True.intro
          let assump_58 := assump_54 assump_76
          apply False.elim assump_58
        case inr assump_55 =>
          have assump_77 : (False → False) := by
            intro assump_66
            apply False.elim assump_66
          let assump_65 := assump_55 assump_77
          apply False.elim assump_65


variable (p2 p1 p5 p4 p7 : Prop)
theorem file9_91112 : (((((True ∧ True) → False) → False) ∨ (((p1 ∧ p2) → False) → False)) ∨ ((((p4 → False) ∧ (p7 → False)) → False) ∧ (((True → False) ∧ (p1 → p7)) ∨ ((p1 → True) ∨ (p5 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_7
  have assump_14 : (True ∧ True) := by
    apply And.intro
    apply True.intro
    apply True.intro
  let assump_10 := assump_7 assump_14
  apply False.elim assump_10


variable (p6 p0 p3 p1 p5 p2 p4 : Prop)
theorem file9_91571 : (((((True ∨ True) ∧ (p1 → p0)) ∨ ((p5 → p3) ∧ (p2 → False))) → (((False → False) ∨ (p5 → False)) → ((p4 ∨ p6) → (p1 ∨ True)))) ∨ ((((False → False) ∧ (False ∧ p6)) ∨ ((True → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_1
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            apply Or.inr
            apply True.intro
          case inr assump_17 =>
            apply Or.inr
            apply True.intro
      case inr assump_13 =>
        cases assump_13
        case intro assump_26 assump_27 =>
          apply Or.inr
          apply True.intro
    case inr assump_9 =>
      cases assump_1
      case inl assump_34 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            apply Or.inr
            apply True.intro
          case inr assump_39 =>
            apply Or.inr
            apply True.intro
      case inr assump_35 =>
        cases assump_35
        case intro assump_48 assump_49 =>
          apply Or.inr
          apply True.intro
  case inr assump_5 =>
    cases assump_2
    case inl assump_56 =>
      cases assump_1
      case inl assump_60 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_62
          case inl assump_64 =>
            apply Or.inr
            apply True.intro
          case inr assump_65 =>
            apply Or.inr
            apply True.intro
      case inr assump_61 =>
        cases assump_61
        case intro assump_74 assump_75 =>
          apply Or.inr
          apply True.intro
    case inr assump_57 =>
      cases assump_1
      case inl assump_82 =>
        cases assump_82
        case intro assump_84 assump_85 =>
          cases assump_84
          case inl assump_86 =>
            apply Or.inr
            apply True.intro
          case inr assump_87 =>
            apply Or.inr
            apply True.intro
      case inr assump_83 =>
        cases assump_83
        case intro assump_96 assump_97 =>
          apply Or.inr
          apply True.intro


variable (p5 p1 p4 p7 p0 : Prop)
theorem file9_93933 : ((((((p7 → p7) ∧ (p4 → p7)) ∨ ((False ∧ p5) → False)) → (((p4 ∨ p4) ∧ (False ∨ p7)) ∨ ((p1 ∧ True) → (p0 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p7 → p7) ∧ (p4 → p7)) ∨ ((False ∧ p5) → False)) → (((p4 ∨ p4) ∧ (False ∨ p7)) ∨ ((p1 ∧ True) → (p0 ∨ True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inr
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply Or.inr
          apply True.intro
    case inr assump_7 =>
      apply Or.inr
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        apply Or.inr
        apply True.intro
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p0 p7 p5 p2 p3 p6 p4 : Prop)
theorem file9_94814 : (((((False ∨ True) → False) → ((p3 ∧ p3) ∧ (p0 → True))) → (((False → p2) → (False ∨ True)) ∨ ((p4 ∨ p3) ∨ (p5 → p7)))) ∨ ((((p3 ∧ p7) ∧ (p0 ∧ True)) ∧ ((False ∧ p6) ∨ (p4 ∧ p7))) ∧ (((p0 → p0) ∧ (p5 ∧ p2)) → ((p4 → False) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  apply True.intro


variable (p7 p5 p2 p3 p4 p0 p6 : Prop)
theorem file9_95226 : ((((((True → p4) ∧ (p4 ∧ p2)) → ((p7 ∧ p5) → (p5 → p7))) ∨ (((p3 ∨ p7) ∧ (p7 → False)) ∨ ((p2 → p0) → (p6 → p6)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((True → p4) ∧ (p4 ∧ p2)) → ((p7 ∧ p5) → (p5 → p7))) ∨ (((p3 ∨ p7) ∧ (p7 → False)) ∨ ((p2 → p0) → (p6 → p6)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          exact assump_10
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p6 p2 p5 p1 p3 p4 p0 : Prop)
theorem file9_95935 : (((((p2 ∨ True) ∨ (p1 → False)) ∨ ((p3 ∧ p1) → False)) → False) → ((((p7 → p5) → (True → p1)) ∨ ((p5 → p1) → (p7 ∨ p3))) → (((p4 ∨ p0) → (False → p6)) → ((p5 ∧ True) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply Or.inr
    intro assump_12
    have assump_30 : (((p2 ∨ True) ∨ (p1 → False)) ∨ ((p3 ∧ p1) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_15 := assump_1 assump_30
    apply False.elim assump_15
  case inr assump_7 =>
    apply Or.inr
    intro assump_23
    have assump_31 : (((p2 ∨ True) ∨ (p1 → False)) ∨ ((p3 ∧ p1) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_26 := assump_1 assump_31
    apply False.elim assump_26


variable (p0 p7 p2 p5 p1 p6 : Prop)
theorem file9_96838 : ((((((p0 ∨ p5) → (p6 ∨ False)) ∧ ((p2 → False) ∧ (False ∧ False))) → (((p1 → False) → False) ∧ ((p7 ∨ False) → (p5 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p0 ∨ p5) → (p6 ∨ False)) ∧ ((p2 → False) ∧ (False ∧ False))) → (((p1 → False) → False) ∧ ((p7 ∨ False) → (p5 ∨ p7)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    intro assump_21
    cases assump_21
    case inl assump_22 =>
      cases assump_5
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            apply False.elim assump_34
    case inr assump_23 =>
      apply False.elim assump_23
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p3 p1 p5 p6 : Prop)
theorem file9_97909 : (((((p6 ∨ False) ∧ (p1 → False)) → ((p6 → False) → (p5 → p3))) → False) → False) := by
  intro assump_1
  have assump_31 : (((p6 ∨ False) ∧ (p1 → False)) → ((p6 → False) → (p5 → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_32 : p6 := by
          exact assump_14
        let assump_22 := assump_6 assump_32
        apply False.elim assump_22
      case inr assump_15 =>
        apply False.elim assump_15
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p2 p4 p7 p6 p0 p3 p1 : Prop)
theorem file9_98593 : (((((p0 ∨ True) ∨ (p7 → p6)) ∧ ((p3 ∧ p2) ∨ (True ∨ p6))) ∨ (((p1 ∧ p4) ∨ (p6 ∧ p2)) ∨ ((p0 ∨ False) → (p1 ∨ p4)))) ∨ ((((p3 → False) → False) ∨ ((p7 ∧ p3) ∧ (p7 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply True.intro
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p7 p1 p4 p2 p5 : Prop)
theorem file9_98985 : ((((((True → False) ∧ (True ∨ p5)) → ((p5 → p4) ∨ (p4 → p4))) ∨ (((p2 ∨ p7) → (p1 ∧ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((True → False) ∧ (True ∨ p5)) → ((p5 → p4) ∨ (p4 → p4))) ∨ (((p2 ∨ p7) → (p1 ∧ p5)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        have assump_37 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_37
        apply False.elim assump_18
      case inr assump_11 =>
        apply Or.inl
        intro assump_24
        have assump_38 : True := by
          apply True.intro
        let assump_29 := assump_6 assump_38
        apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p7 p5 p2 p4 p0 p1 p6 : Prop)
theorem file9_99917 : (((((p4 → p2) ∧ (True → False)) → ((p0 → p2) → False)) ∨ (((p7 → False) ∧ (p7 → True)) → False)) ∧ ((((p1 → p5) → (True ∨ p1)) ∧ ((True → False) → (p4 ∧ p5))) ∨ (((p0 ∧ p1) → (p6 → False)) ∧ ((p7 → p5) → (False ∨ p6))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_31 : True := by
      apply True.intro
    let assump_11 := assump_6 assump_31
    apply False.elim assump_11
  apply Or.inl
  apply And.intro
  intro assump_15
  apply Or.inl
  apply True.intro
  intro assump_18
  apply And.intro
  have assump_32 : True := by
    apply True.intro
  let assump_21 := assump_18 assump_32
  apply False.elim assump_21
  have assump_33 : True := by
    apply True.intro
  let assump_27 := assump_18 assump_33
  apply False.elim assump_27


variable (p0 p7 p4 p5 p1 : Prop)
theorem file9_100804 : (((((p7 ∧ False) → False) → False) → False) → ((((p0 → False) → (True ∨ p5)) ∨ ((False → False) ∨ (p4 → p7))) ∨ (((p1 → False) ∧ (p7 ∧ p5)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inl
  apply True.intro


variable (p0 p5 p1 p7 p3 p2 : Prop)
theorem file9_101119 : (((((p0 ∨ p0) → (True ∨ p3)) → False) ∨ (((p0 → False) → (p3 ∨ True)) → False)) → ((((False → p1) → (p7 → p3)) ∧ ((p7 ∧ p0) → False)) ∨ (((p5 ∧ p1) ∧ (p2 → p5)) ∧ ((p3 ∧ False) ∧ (p7 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply And.intro
    intro assump_6
    intro assump_7
    have assump_78 : ((p0 ∨ p0) → (True ∨ p3)) := by
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        apply Or.inl
        apply True.intro
      case inr assump_17 =>
        apply Or.inl
        apply True.intro
    let assump_14 := assump_2 assump_78
    apply False.elim assump_14
    intro assump_25
    cases assump_25
    case intro assump_26 assump_27 =>
      have assump_79 : ((p0 ∨ p0) → (True ∨ p3)) := by
        intro assump_35
        cases assump_35
        case inl assump_36 =>
          apply Or.inl
          apply True.intro
        case inr assump_37 =>
          apply Or.inl
          apply True.intro
      let assump_34 := assump_2 assump_79
      apply False.elim assump_34
  case inr assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_47
    intro assump_48
    have assump_80 : ((p0 → False) → (p3 ∨ True)) := by
      intro assump_56
      apply Or.inr
      apply True.intro
    let assump_55 := assump_3 assump_80
    apply False.elim assump_55
    intro assump_62
    cases assump_62
    case intro assump_63 assump_64 =>
      have assump_81 : ((p0 → False) → (p3 ∨ True)) := by
        intro assump_72
        apply Or.inr
        apply True.intro
      let assump_71 := assump_3 assump_81
      apply False.elim assump_71


variable (p2 p7 : Prop)
theorem file9_102805 : ((((((False → p7) ∨ (False ∨ p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p7) ∨ (False ∨ p2)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → p7) ∨ (False ∨ p2)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p2 p1 : Prop)
theorem file9_103309 : (((((p2 ∧ p1) ∨ (p1 → False)) → ((p7 ∧ p2) → (p3 ∨ True))) → False) → False) := by
  intro assump_11
  have assump_36 : (((p2 ∧ p1) ∨ (p1 → False)) → ((p7 ∧ p2) → (p3 ∨ True))) := by
    intro assump_15
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      cases assump_15
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply Or.inr
          apply True.intro
      case inr assump_24 =>
        apply Or.inr
        apply True.intro
  let assump_14 := assump_11 assump_36
  apply False.elim assump_14


variable (p6 p3 p7 p1 : Prop)
theorem file9_103952 : (((((p7 ∨ True) → False) ∧ ((p1 ∧ True) → False)) → (((p7 ∧ p3) ∨ (p3 → True)) ∨ ((p6 ∧ True) → (p1 ∧ p1)))) ∨ ((((p7 ∧ p3) ∧ (p7 → p6)) ∨ ((p7 → False) ∧ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply True.intro


variable (p4 p2 p3 p5 p1 p7 : Prop)
theorem file9_104355 : ((((((True ∧ False) ∧ (p1 ∧ True)) → ((p4 → True) → (p7 → p7))) ∧ (((p5 ∨ p7) ∨ (p5 ∧ p4)) → ((p2 ∨ p2) → (p4 ∨ p2)))) → ((((p5 → False) → (p3 → p3)) → False) ∧ (((p2 → False) ∧ (p3 → True)) ∨ ((p5 ∧ p5) → (False ∨ p2))))) → False) := by
  intro assump_1
  have assump_67 : ((((True ∧ False) ∧ (p1 ∧ True)) → ((p4 → True) → (p7 → p7))) ∧ (((p5 ∨ p7) ∨ (p5 ∧ p4)) → ((p2 ∨ p2) → (p4 ∨ p2)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    intro assump_20
    intro assump_21
    cases assump_21
    case inl assump_22 =>
      cases assump_20
      case inl assump_26 =>
        cases assump_26
        case inl assump_28 =>
          apply Or.inr
          exact assump_22
        case inr assump_29 =>
          apply Or.inr
          exact assump_22
      case inr assump_27 =>
        cases assump_27
        case intro assump_34 assump_35 =>
          apply Or.inl
          exact assump_35
    case inr assump_23 =>
      cases assump_20
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          apply Or.inr
          exact assump_23
        case inr assump_45 =>
          apply Or.inr
          exact assump_23
      case inr assump_43 =>
        cases assump_43
        case intro assump_50 assump_51 =>
          apply Or.inl
          exact assump_51
  let assump_4 := assump_1 assump_67
  let assump_56 := And.left assump_4
  have assump_68 : ((p5 → False) → (p3 → p3)) := by
    intro assump_58
    intro assump_59
    exact assump_59
  let assump_57 := assump_56 assump_68
  apply False.elim assump_57


variable (p5 p3 p6 p4 p1 p2 p0 : Prop)
theorem file9_106162 : (((((p6 → False) ∨ (p0 ∨ p3)) ∨ ((p5 → True) ∧ (p4 → p2))) → (((False ∧ p4) ∨ (p3 → False)) → ((p5 → True) ∨ (p1 → False)))) ∨ ((((p5 ∨ p4) ∧ (True → False)) ∧ ((p6 → False) → (p5 → p6))) → False)) := by
  apply Or.inl
  intro assump_22
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      apply False.elim assump_26
  case inr assump_25 =>
    cases assump_22
    case inl assump_32 =>
      cases assump_32
      case inl assump_34 =>
        apply Or.inl
        intro assump_38
        apply True.intro
      case inr assump_35 =>
        cases assump_35
        case inl assump_39 =>
          apply Or.inl
          intro assump_43
          apply True.intro
        case inr assump_40 =>
          apply Or.inl
          intro assump_46
          apply True.intro
    case inr assump_33 =>
      cases assump_33
      case intro assump_47 assump_48 =>
        apply Or.inl
        intro assump_53
        apply True.intro


variable (p1 p6 p7 p2 : Prop)
theorem file9_107216 : (((((True ∨ p2) ∨ (p6 → False)) → ((p2 ∧ p7) → (p1 → p7))) → False) → False) := by
  intro assump_18
  have assump_46 : (((True ∨ p2) ∨ (p6 → False)) → ((p2 ∧ p7) → (p1 → p7))) := by
    intro assump_22
    intro assump_23
    intro assump_24
    cases assump_23
    case intro assump_27 assump_28 =>
      cases assump_22
      case inl assump_33 =>
        cases assump_33
        case inl assump_35 =>
          exact assump_28
        case inr assump_36 =>
          exact assump_28
      case inr assump_34 =>
        exact assump_28
  let assump_21 := assump_18 assump_46
  apply False.elim assump_21


variable (p7 p5 p4 p3 : Prop)
theorem file9_107877 : (((((False → False) ∨ (True → p3)) ∨ ((False ∧ p5) ∧ (False → False))) ∧ (((False → False) ∨ (p7 ∧ p4)) → False)) → ((((p7 → p5) → (True → False)) → False) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        have assump_43 : ((False → False) ∨ (p7 ∧ p4)) := by
          apply Or.inl
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_10 assump_43
        apply False.elim assump_19
      case inr assump_14 =>
        have assump_44 : ((False → False) ∨ (p7 ∧ p4)) := by
          apply Or.inl
          intro assump_31
          apply False.elim assump_31
        let assump_30 := assump_10 assump_44
        apply False.elim assump_30
    case inr assump_12 =>
      cases assump_12
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          apply False.elim assump_39


variable (p7 p2 p5 p6 p1 : Prop)
theorem file9_108960 : (((((p1 ∧ p6) ∧ (p7 → False)) ∧ ((True ∨ p6) ∧ (p5 → p1))) ∨ (((False ∨ p5) → False) ∨ ((p2 → p1) ∧ (p6 ∧ p2)))) → ((((p5 ∧ False) → (False ∧ True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_8
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              have assump_103 : ((p5 ∧ False) → (False ∧ True)) := by
                intro assump_32
                apply And.intro
                cases assump_32
                case intro assump_33 assump_34 =>
                  apply False.elim assump_34
                apply True.intro
              let assump_31 := assump_2 assump_103
              apply False.elim assump_31
            case inr assump_22 =>
              have assump_104 : ((p5 ∧ False) → (False ∧ True)) := by
                intro assump_52
                apply And.intro
                cases assump_52
                case intro assump_53 assump_54 =>
                  apply False.elim assump_54
                apply True.intro
              let assump_51 := assump_2 assump_104
              apply False.elim assump_51
  case inr assump_6 =>
    cases assump_6
    case inl assump_62 =>
      have assump_105 : ((p5 ∧ False) → (False ∧ True)) := by
        intro assump_68
        apply And.intro
        cases assump_68
        case intro assump_69 assump_70 =>
          apply False.elim assump_70
        apply True.intro
      let assump_67 := assump_2 assump_105
      apply False.elim assump_67
    case inr assump_63 =>
      cases assump_63
      case intro assump_78 assump_79 =>
        cases assump_79
        case intro assump_82 assump_83 =>
          have assump_106 : ((p5 ∧ False) → (False ∧ True)) := by
            intro assump_93
            apply And.intro
            cases assump_93
            case intro assump_94 assump_95 =>
              apply False.elim assump_95
            apply True.intro
          let assump_92 := assump_2 assump_106
          apply False.elim assump_92


variable (p3 p5 p1 p7 p6 p2 p4 : Prop)
theorem file9_111274 : (((((p1 ∧ True) → (False → False)) ∨ ((p4 ∧ p6) ∨ (p3 ∧ p4))) ∨ (((p4 ∧ p3) ∨ (p7 → False)) → False)) ∨ ((((p1 → p7) ∨ (True → p7)) → False) → (((p1 → p6) ∨ (p2 → p7)) ∧ ((p5 ∧ p6) ∨ (p7 → p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_103
  intro assump_104
  apply False.elim assump_104


variable (p2 p3 p0 p1 : Prop)
theorem file9_111644 : (((((p0 → p0) ∨ (p2 ∧ False)) → False) → False) ∨ ((((p3 → p3) → False) ∨ ((p3 → True) → (p1 → p0))) → False)) := by
  apply Or.inl
  intro assump_4
  have assump_14 : ((p0 → p0) ∨ (p2 ∧ False)) := by
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p7 p0 p3 p4 p5 p6 p1 : Prop)
theorem file9_112028 : (((((p0 ∨ p5) → False) ∧ ((p7 ∨ p5) ∨ (p7 → False))) ∧ (((False ∨ p6) ∨ (p0 → True)) ∧ ((p1 ∨ False) → (True ∧ p0)))) → ((((False ∨ p4) ∨ (p4 ∧ p5)) ∧ ((p0 → False) → (p3 ∨ False))) ∨ (((True → False) → False) ∨ ((p3 ∨ p0) → (False → False))))) := by
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
              cases assump_16
              case inl assump_18 =>
                apply False.elim assump_18
              case inr assump_19 =>
                apply Or.inr
                apply Or.inl
                intro assump_26
                have assump_108 : True := by
                  apply True.intro
                let assump_29 := assump_26 assump_108
                apply False.elim assump_29
            case inr assump_17 =>
              apply Or.inr
              apply Or.inl
              intro assump_37
              have assump_109 : True := by
                apply True.intro
              let assump_40 := assump_37 assump_109
              apply False.elim assump_40
        case inr assump_11 =>
          cases assump_3
          case intro assump_46 assump_47 =>
            cases assump_46
            case inl assump_48 =>
              cases assump_48
              case inl assump_50 =>
                apply False.elim assump_50
              case inr assump_51 =>
                apply Or.inr
                apply Or.inl
                intro assump_58
                have assump_110 : True := by
                  apply True.intro
                let assump_61 := assump_58 assump_110
                apply False.elim assump_61
            case inr assump_49 =>
              apply Or.inr
              apply Or.inl
              intro assump_69
              have assump_111 : True := by
                apply True.intro
              let assump_72 := assump_69 assump_111
              apply False.elim assump_72
      case inr assump_9 =>
        cases assump_3
        case intro assump_78 assump_79 =>
          cases assump_78
          case inl assump_80 =>
            cases assump_80
            case inl assump_82 =>
              apply False.elim assump_82
            case inr assump_83 =>
              apply Or.inr
              apply Or.inl
              intro assump_90
              have assump_112 : True := by
                apply True.intro
              let assump_93 := assump_90 assump_112
              apply False.elim assump_93
          case inr assump_81 =>
            apply Or.inr
            apply Or.inl
            intro assump_101
            have assump_113 : True := by
              apply True.intro
            let assump_104 := assump_101 assump_113
            apply False.elim assump_104


variable (p1 p7 p5 p4 p2 p3 p6 p0 : Prop)
theorem file9_115074 : ((((((p0 ∨ p1) → False) → False) ∧ (((p4 ∧ p7) ∨ (p6 ∨ p3)) ∧ ((p0 ∨ True) ∧ (False ∧ True)))) ∧ ((((p5 → p2) → (p4 → False)) → False) ∧ (((p0 ∨ p6) ∨ (False ∨ False)) ∨ ((p7 ∨ False) ∨ (p3 → False))))) → False) := by
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_20
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        cases assump_26
        case inl assump_28 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            cases assump_27
            case intro assump_36 assump_37 =>
              cases assump_36
              case inl assump_38 =>
                cases assump_37
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42
              case inr assump_39 =>
                cases assump_37
                case intro assump_48 assump_49 =>
                  apply False.elim assump_48
        case inr assump_29 =>
          cases assump_29
          case inl assump_52 =>
            cases assump_27
            case intro assump_56 assump_57 =>
              cases assump_56
              case inl assump_58 =>
                cases assump_57
                case intro assump_62 assump_63 =>
                  apply False.elim assump_62
              case inr assump_59 =>
                cases assump_57
                case intro assump_68 assump_69 =>
                  apply False.elim assump_68
          case inr assump_53 =>
            cases assump_27
            case intro assump_74 assump_75 =>
              cases assump_74
              case inl assump_76 =>
                cases assump_75
                case intro assump_80 assump_81 =>
                  apply False.elim assump_80
              case inr assump_77 =>
                cases assump_75
                case intro assump_86 assump_87 =>
                  apply False.elim assump_86


variable (p4 p5 p2 p6 p0 : Prop)
theorem file9_117075 : (((((p4 ∧ p2) → False) ∧ ((p4 → p0) → False)) ∧ (((p6 ∨ p0) → (p5 ∧ p0)) ∧ ((p2 ∨ p4) → False))) → ((((p6 → False) → False) → ((False ∧ p4) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        have assump_33 : (p4 → p0) := by
          intro assump_22
          have assump_34 : (p2 ∨ p4) := by
            apply Or.inr
            exact assump_22
          let assump_26 := assump_14 assump_34
          apply False.elim assump_26
        let assump_21 := assump_8 assump_33
        apply False.elim assump_21


variable (p1 p7 p3 p0 p4 : Prop)
theorem file9_117825 : ((((((p1 → p4) ∧ (p4 ∧ p3)) ∧ ((True → False) ∧ (p0 ∨ p7))) → False) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p1 → p4) ∧ (p4 ∧ p3)) ∧ ((True → False) ∧ (p0 ∨ p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              have assump_42 : True := by
                apply True.intro
              let assump_27 := assump_18 assump_42
              apply False.elim assump_27
            case inr assump_23 =>
              have assump_43 : True := by
                apply True.intro
              let assump_34 := assump_18 assump_43
              apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p5 p7 p6 p3 p1 p2 p0 p4 : Prop)
theorem file9_118855 : ((((((p0 → False) → (p5 ∨ p6)) → ((True → p6) → (p6 → p1))) ∧ (((p4 → False) → (False ∨ p3)) ∨ ((p4 ∨ p1) → (p5 ∧ p1)))) ∧ ((((p7 ∧ False) → (p5 ∧ p0)) ∨ ((p2 ∨ p4) ∨ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_52 : (((p7 ∧ False) → (p5 ∧ p0)) ∨ ((p2 ∨ p4) ∨ (p4 → False))) := by
          apply Or.inl
          intro assump_15
          apply And.intro
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
        let assump_14 := assump_3 assump_52
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_53 : (((p7 ∧ False) → (p5 ∧ p0)) ∨ ((p2 ∨ p4) ∨ (p4 → False))) := by
          apply Or.inl
          intro assump_36
          apply And.intro
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_38
          cases assump_36
          case intro assump_43 assump_44 =>
            apply False.elim assump_44
        let assump_35 := assump_3 assump_53
        apply False.elim assump_35


variable (p0 p5 p6 p3 p7 p2 p4 p1 : Prop)
theorem file9_120248 : (((((p3 ∧ p5) → False) ∧ ((p4 ∨ p6) ∧ (p4 → p0))) → (((p4 ∧ p3) ∧ (p1 ∨ p4)) ∨ ((p7 ∨ True) ∨ (p3 ∧ p3)))) ∨ ((((p5 ∧ p5) ∨ (False ∨ p3)) ∨ ((p5 ∧ p7) ∨ (p2 → False))) ∧ (((p5 → p6) ∨ (p3 → False)) → False))) := by
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_21 =>
        apply Or.inr
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p0 p6 p5 p4 p2 p7 p1 : Prop)
theorem file9_120925 : (((((p0 ∨ False) ∨ (p7 → False)) ∧ ((p5 ∨ p0) ∧ (True → False))) → (((p2 → False) ∨ (False ∧ p6)) → ((p4 ∧ p1) → False))) ∧ ((((p2 → p2) ∧ (p7 → p7)) → False) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                have assump_83 : True := by
                  apply True.intro
                let assump_30 := assump_23 assump_83
                apply False.elim assump_30
              case inr assump_25 =>
                have assump_84 : True := by
                  apply True.intro
                let assump_38 := assump_23 assump_84
                apply False.elim assump_38
          case inr assump_19 =>
            apply False.elim assump_19
        case inr assump_17 =>
          cases assump_15
          case intro assump_46 assump_47 =>
            cases assump_46
            case inl assump_48 =>
              have assump_85 : True := by
                apply True.intro
              let assump_54 := assump_47 assump_85
              apply False.elim assump_54
            case inr assump_49 =>
              have assump_86 : True := by
                apply True.intro
              let assump_62 := assump_47 assump_86
              apply False.elim assump_62
    case inr assump_11 =>
      cases assump_11
      case intro assump_66 assump_67 =>
        apply False.elim assump_66
  intro assump_70
  have assump_87 : ((p2 → p2) ∧ (p7 → p7)) := by
    apply And.intro
    intro assump_74
    exact assump_74
    intro assump_77
    exact assump_77
  let assump_73 := assump_70 assump_87
  apply False.elim assump_73


variable (p7 p3 p4 p6 p1 p2 p0 : Prop)
theorem file9_122986 : (((((True → False) → False) ∨ ((p7 → p1) ∧ (p3 → False))) ∨ (((p1 ∧ p4) → False) → False)) ∨ ((((False → False) → False) → False) → (((p3 → p6) → (p0 ∧ p3)) ∨ ((p3 ∨ p4) ∧ (p2 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p7 p1 p5 p6 p0 : Prop)
theorem file9_123417 : (((((p0 ∨ p6) → (True ∨ p5)) → False) ∧ (((p2 → False) → (p2 → False)) → ((p7 ∨ True) → (p2 → False)))) → ((((p6 ∨ p5) → (p6 ∨ False)) ∨ ((True → p2) → False)) → (((p5 → p6) ∨ (p1 ∨ p0)) → ((p6 ∧ p1) ∨ (p7 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_1
      case intro assump_12 assump_13 =>
        have assump_212 : ((p0 ∨ p6) → (True ∨ p5)) := by
          intro assump_32
          cases assump_32
          case inl assump_33 =>
            apply Or.inl
            apply True.intro
          case inr assump_34 =>
            apply Or.inl
            apply True.intro
        let assump_31 := assump_12 assump_212
        apply False.elim assump_31
    case inr assump_9 =>
      cases assump_1
      case intro assump_44 assump_45 =>
        have assump_213 : ((p0 ∨ p6) → (True ∨ p5)) := by
          intro assump_64
          cases assump_64
          case inl assump_65 =>
            apply Or.inl
            apply True.intro
          case inr assump_66 =>
            apply Or.inl
            apply True.intro
        let assump_63 := assump_44 assump_213
        apply False.elim assump_63
  case inr assump_5 =>
    cases assump_5
    case inl assump_74 =>
      cases assump_2
      case inl assump_78 =>
        cases assump_1
        case intro assump_82 assump_83 =>
          have assump_214 : ((p0 ∨ p6) → (True ∨ p5)) := by
            intro assump_102
            cases assump_102
            case inl assump_103 =>
              apply Or.inl
              apply True.intro
            case inr assump_104 =>
              apply Or.inl
              apply True.intro
          let assump_101 := assump_82 assump_214
          apply False.elim assump_101
      case inr assump_79 =>
        cases assump_1
        case intro assump_114 assump_115 =>
          have assump_215 : ((p0 ∨ p6) → (True ∨ p5)) := by
            intro assump_134
            cases assump_134
            case inl assump_135 =>
              apply Or.inl
              apply True.intro
            case inr assump_136 =>
              apply Or.inl
              apply True.intro
          let assump_133 := assump_114 assump_215
          apply False.elim assump_133
    case inr assump_75 =>
      cases assump_2
      case inl assump_146 =>
        cases assump_1
        case intro assump_150 assump_151 =>
          have assump_216 : ((p0 ∨ p6) → (True ∨ p5)) := by
            intro assump_170
            cases assump_170
            case inl assump_171 =>
              apply Or.inl
              apply True.intro
            case inr assump_172 =>
              apply Or.inl
              apply True.intro
          let assump_169 := assump_150 assump_216
          apply False.elim assump_169
      case inr assump_147 =>
        cases assump_1
        case intro assump_182 assump_183 =>
          have assump_217 : ((p0 ∨ p6) → (True ∨ p5)) := by
            intro assump_202
            cases assump_202
            case inl assump_203 =>
              apply Or.inl
              apply True.intro
            case inr assump_204 =>
              apply Or.inl
              apply True.intro
          let assump_201 := assump_182 assump_217
          apply False.elim assump_201


variable (p5 p1 p0 : Prop)
theorem file9_126781 : ((((((True ∧ False) ∧ (p1 → p0)) ∧ ((p5 → True) → (True ∨ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True ∧ False) ∧ (p1 → p0)) ∧ ((p5 → True) → (True ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p2 p0 p5 p6 p7 : Prop)
theorem file9_127351 : ((((((p2 → p2) ∨ (False → False)) ∧ ((p5 ∧ p0) ∨ (p6 → p6))) ∨ (((p4 ∨ p5) → (p7 ∧ p0)) → ((p0 → p4) → (p6 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 → p2) ∨ (False → False)) ∧ ((p5 ∧ p0) ∨ (p6 → p6))) ∨ (((p4 ∨ p5) → (p7 ∧ p0)) → ((p0 → p4) → (p6 ∨ True)))) := by
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_5
    exact assump_5
    apply Or.inr
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p5 p4 p3 p6 p1 p7 p0 : Prop)
theorem file9_127929 : (((((p1 ∧ p1) → (p6 ∨ True)) ∨ ((p2 → p7) → (p0 ∧ p4))) ∨ (((False → False) ∨ (p4 → False)) ∨ ((p3 ∨ p5) ∧ (False → False)))) ∨ ((((p5 ∧ p4) ∧ (p0 → p6)) ∧ ((p6 ∨ p0) → (False ∧ p2))) → (((True → p2) → (p4 ∧ True)) ∧ ((p0 ∧ p2) ∨ (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inr
    apply True.intro


variable (p4 p0 p2 p6 : Prop)
theorem file9_128387 : (((((p2 → p0) → (p6 → True)) ∨ ((p2 ∧ p4) → False)) → False) → False) := by
  intro assump_1
  have assump_10 : (((p2 → p0) → (p6 → True)) ∨ ((p2 ∧ p4) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


