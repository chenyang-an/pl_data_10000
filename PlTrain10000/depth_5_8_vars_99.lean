variable (p6 p7 p5 p4 p2 p3 : Prop)
theorem file99_44 : (((((p5 → p5) ∧ (True → False)) → ((p5 ∧ p2) → (True → p2))) → False) → ((((False ∧ True) ∧ (p2 → p7)) → ((p5 ∨ p6) → False)) ∧ (((p3 ∨ p2) ∧ (p4 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  case inr assump_5 =>
    cases assump_2
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case inl assump_25 =>
      have assump_81 : (((p5 → p5) ∧ (True → False)) → ((p5 ∧ p2) → (True → p2))) := by
        intro assump_34
        intro assump_35
        intro assump_36
        cases assump_35
        case intro assump_39 assump_40 =>
          cases assump_34
          case intro assump_45 assump_46 =>
            exact assump_40
      let assump_33 := assump_1 assump_81
      apply False.elim assump_33
    case inr assump_26 =>
      have assump_82 : (((p5 → p5) ∧ (True → False)) → ((p5 ∧ p2) → (True → p2))) := by
        intro assump_61
        intro assump_62
        intro assump_63
        cases assump_62
        case intro assump_66 assump_67 =>
          cases assump_61
          case intro assump_72 assump_73 =>
            exact assump_67
      let assump_60 := assump_1 assump_82
      apply False.elim assump_60


variable (p4 p5 p6 p0 p7 : Prop)
theorem file99_1653 : ((((((False → False) ∨ (p0 ∨ False)) ∨ ((p5 → False) ∨ (False → p7))) ∨ (((p4 ∧ p6) ∨ (p4 → False)) ∨ ((p4 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p0 ∨ False)) ∨ ((p5 → False) ∨ (False → p7))) ∨ (((p4 ∧ p6) ∨ (p4 → False)) ∨ ((p4 → p0) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p1 p6 p7 : Prop)
theorem file99_2184 : ((((((p6 ∨ False) ∨ (p6 → p1)) ∨ ((p6 ∧ p5) ∧ (p6 → p7))) → (((True → False) ∨ (True ∧ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p6 ∨ False) ∨ (p6 → p1)) ∨ ((p6 ∧ p5) ∧ (p6 → p7))) → (((True → False) ∨ (True ∧ False)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            have assump_61 : True := by
              apply True.intro
            let assump_20 := assump_7 assump_61
            apply False.elim assump_20
          case inr assump_16 =>
            apply False.elim assump_16
        case inr assump_14 =>
          have assump_62 : True := by
            apply True.intro
          let assump_29 := assump_7 assump_62
          apply False.elim assump_29
      case inr assump_12 =>
        cases assump_12
        case intro assump_33 assump_34 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            have assump_63 : True := by
              apply True.intro
            let assump_47 := assump_7 assump_63
            apply False.elim assump_47
    case inr assump_8 =>
      cases assump_8
      case intro assump_51 assump_52 =>
        apply False.elim assump_52
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p3 p1 p2 : Prop)
theorem file99_3669 : (((((True ∧ p3) ∨ (p3 → False)) ∨ ((p2 ∧ p1) ∨ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((True ∧ p3) ∨ (p3 → False)) ∨ ((p2 ∧ p1) ∨ (p1 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((True ∧ p3) ∨ (p3 → False)) ∨ ((p2 ∧ p1) ∨ (p1 → False))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      apply True.intro
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p3 p0 p7 p4 p1 : Prop)
theorem file99_4295 : (((((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) → False) → ((((p4 ∧ False) → False) → ((p3 → True) ∨ (p7 ∧ p4))) → (((p1 → False) ∨ (p5 ∨ p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_54 : (((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_13
      have assump_55 : (((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_13
      let assump_17 := assump_1 assump_55
      apply False.elim assump_17
    let assump_12 := assump_1 assump_54
    apply False.elim assump_12
  case inr assump_5 =>
    cases assump_5
    case inl assump_24 =>
      have assump_56 : (((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
        apply Or.inl
        apply Or.inr
        intro assump_33
        have assump_57 : (((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_33
        let assump_37 := assump_1 assump_57
        apply False.elim assump_37
      let assump_32 := assump_1 assump_56
      apply False.elim assump_32
    case inr assump_25 =>
      have assump_58 : (((p3 ∨ False) ∨ (p3 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → False))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_25
      let assump_50 := assump_1 assump_58
      apply False.elim assump_50


variable (p5 p3 p6 p2 p4 p1 p7 p0 : Prop)
theorem file99_5941 : (((((p7 ∧ False) ∧ (p2 ∨ p4)) ∨ ((p3 → False) → (p1 ∧ p3))) ∨ (((False ∨ p7) → False) ∧ ((p0 → False) ∧ (True → False)))) → ((((p3 ∨ p5) → False) ∨ ((p6 → False) ∧ (p1 ∨ p5))) → (((p5 ∧ True) ∧ (p0 → False)) → ((p0 → p5) ∨ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_14 =>
        cases assump_1
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                apply False.elim assump_25
          case inr assump_21 =>
            apply Or.inl
            intro assump_32
            exact assump_6
        case inr assump_19 =>
          cases assump_19
          case intro assump_35 assump_36 =>
            cases assump_36
            case intro assump_39 assump_40 =>
              apply Or.inl
              intro assump_45
              exact assump_6
      case inr assump_15 =>
        cases assump_15
        case intro assump_48 assump_49 =>
          cases assump_49
          case inl assump_52 =>
            cases assump_1
            case inl assump_56 =>
              cases assump_56
              case inl assump_58 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    apply False.elim assump_63
              case inr assump_59 =>
                apply Or.inl
                intro assump_70
                exact assump_6
            case inr assump_57 =>
              cases assump_57
              case intro assump_73 assump_74 =>
                cases assump_74
                case intro assump_77 assump_78 =>
                  apply Or.inl
                  intro assump_83
                  exact assump_6
          case inr assump_53 =>
            cases assump_1
            case inl assump_88 =>
              cases assump_88
              case inl assump_90 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  cases assump_92
                  case intro assump_94 assump_95 =>
                    apply False.elim assump_95
              case inr assump_91 =>
                apply Or.inl
                intro assump_102
                exact assump_53
            case inr assump_89 =>
              cases assump_89
              case intro assump_105 assump_106 =>
                cases assump_106
                case intro assump_109 assump_110 =>
                  apply Or.inl
                  intro assump_115
                  exact assump_53


variable (p4 p2 p3 p5 p0 p7 p6 : Prop)
theorem file99_8851 : ((((((p2 ∧ p3) ∧ (p5 → p4)) ∧ ((p6 ∨ p7) → (p0 → False))) → (((p3 → p3) → False) → ((p0 ∧ p7) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p2 ∧ p3) ∧ (p5 → p4)) ∧ ((p6 ∨ p7) → (p0 → False))) → (((p3 → p3) → False) → ((p0 ∧ p7) → (True → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            have assump_42 : (p6 ∨ p7) := by
              apply Or.inr
              exact assump_12
            let assump_33 := assump_20 assump_42
            have assump_43 : p0 := by
              exact assump_11
            let assump_34 := assump_33 assump_43
            apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p1 p5 p0 p7 p2 p4 : Prop)
theorem file99_9905 : (((((p0 → p2) → False) → ((False → False) → (p4 → False))) → False) → ((((False ∧ p1) → False) ∧ ((p1 ∨ False) ∨ (False → False))) ∨ (((p5 ∨ True) ∧ (p7 → False)) ∨ ((p4 ∧ p1) ∧ (p2 ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  apply Or.inr
  intro assump_9
  apply False.elim assump_9


variable (p6 p3 p1 p4 p5 p2 p0 : Prop)
theorem file99_10374 : (((((p3 ∧ False) ∧ (p1 → p3)) ∨ ((False ∧ p6) → (p5 → False))) ∨ (((p0 → False) ∨ (p1 → False)) → ((False → False) → (True → p2)))) ∧ ((((p0 ∨ True) ∧ (p5 ∧ False)) ∨ ((True ∨ p1) → False)) → (((False ∧ False) ∧ (p4 ∨ p5)) → ((p1 → False) ∧ (True ∧ False))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  intro assump_22
  intro assump_23
  cases assump_22
  case intro assump_26 assump_27 =>
    apply False.elim assump_26
  intro assump_30
  intro assump_31
  apply And.intro
  intro assump_32
  cases assump_31
  case intro assump_35 assump_36 =>
    cases assump_35
    case intro assump_37 assump_38 =>
      apply False.elim assump_37
  apply And.intro
  apply True.intro
  cases assump_31
  case intro assump_41 assump_42 =>
    cases assump_41
    case intro assump_43 assump_44 =>
      apply False.elim assump_43


variable (p0 p5 p6 p3 p4 p7 : Prop)
theorem file99_11268 : (((((p5 → p5) ∧ (p4 ∧ p6)) ∧ ((p0 ∨ p7) → False)) ∧ (((p7 → True) → (p3 → False)) ∧ ((p4 ∨ p3) ∨ (p3 ∨ p3)))) → ((((False → False) ∨ (p7 → p4)) → False) → (((p6 ∨ p3) ∧ (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_15
              case intro assump_30 assump_31 =>
                cases assump_31
                case inl assump_34 =>
                  cases assump_34
                  case inl assump_36 =>
                    have assump_152 : ((False → False) ∨ (p7 → p4)) := by
                      apply Or.inl
                      intro assump_49
                      apply False.elim assump_49
                    let assump_48 := assump_2 assump_152
                    apply False.elim assump_48
                  case inr assump_37 =>
                    have assump_153 : (p7 → True) := by
                      intro assump_59
                      apply True.intro
                    let assump_58 := assump_30 assump_153
                    have assump_154 : p3 := by
                      exact assump_37
                    let assump_60 := assump_58 assump_154
                    apply False.elim assump_60
                case inr assump_35 =>
                  cases assump_35
                  case inl assump_64 =>
                    have assump_155 : (p7 → True) := by
                      intro assump_70
                      apply True.intro
                    let assump_69 := assump_30 assump_155
                    have assump_156 : p3 := by
                      exact assump_64
                    let assump_71 := assump_69 assump_156
                    apply False.elim assump_71
                  case inr assump_65 =>
                    have assump_157 : (p7 → True) := by
                      intro assump_79
                      apply True.intro
                    let assump_78 := assump_30 assump_157
                    have assump_158 : p3 := by
                      exact assump_65
                    let assump_80 := assump_78 assump_158
                    apply False.elim assump_80
    case inr assump_7 =>
      cases assump_1
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            cases assump_95
            case intro assump_98 assump_99 =>
              cases assump_91
              case intro assump_106 assump_107 =>
                cases assump_107
                case inl assump_110 =>
                  cases assump_110
                  case inl assump_112 =>
                    have assump_159 : (p7 → True) := by
                      intro assump_118
                      apply True.intro
                    let assump_117 := assump_106 assump_159
                    have assump_160 : p3 := by
                      exact assump_7
                    let assump_119 := assump_117 assump_160
                    apply False.elim assump_119
                  case inr assump_113 =>
                    have assump_161 : (p7 → True) := by
                      intro assump_127
                      apply True.intro
                    let assump_126 := assump_106 assump_161
                    have assump_162 : p3 := by
                      exact assump_113
                    let assump_128 := assump_126 assump_162
                    apply False.elim assump_128
                case inr assump_111 =>
                  cases assump_111
                  case inl assump_132 =>
                    have assump_163 : (p7 → True) := by
                      intro assump_138
                      apply True.intro
                    let assump_137 := assump_106 assump_163
                    have assump_164 : p3 := by
                      exact assump_132
                    let assump_139 := assump_137 assump_164
                    apply False.elim assump_139
                  case inr assump_133 =>
                    have assump_165 : (p7 → True) := by
                      intro assump_147
                      apply True.intro
                    let assump_146 := assump_106 assump_165
                    have assump_166 : p3 := by
                      exact assump_133
                    let assump_148 := assump_146 assump_166
                    apply False.elim assump_148


variable (p5 p1 p4 p3 : Prop)
theorem file99_16069 : ((((((p1 → False) → (p3 → True)) ∧ ((p4 ∧ False) → False)) → False) ∨ ((((p4 → False) → False) → ((True ∨ p5) → (True ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_37 : (((p1 → False) → (p3 → True)) ∧ ((p4 ∧ False) → False)) := by
      apply And.intro
      intro assump_7
      intro assump_8
      apply True.intro
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_6 := assump_2 assump_37
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_38 : (((p4 → False) → False) → ((True ∨ p5) → (True ∨ True))) := by
      intro assump_22
      intro assump_23
      cases assump_23
      case inl assump_24 =>
        apply Or.inl
        apply True.intro
      case inr assump_25 =>
        apply Or.inl
        apply True.intro
    let assump_21 := assump_3 assump_38
    apply False.elim assump_21


variable (p7 p0 p3 p1 : Prop)
theorem file99_17081 : ((((((p3 → p1) → (False → p7)) → ((p0 → False) ∧ (p0 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p3 → p1) → (False → p7)) → ((p0 → False) ∧ (p0 ∧ False))) → False) := by
    intro assump_5
    have assump_24 : ((p3 → p1) → (False → p7)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_24
    let assump_13 := And.right assump_8
    let assump_15 := And.right assump_13
    apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p3 p1 p0 p4 p6 p5 : Prop)
theorem file99_17719 : (((((p0 ∨ p5) → False) → False) ∧ (((True ∨ p3) ∧ (p2 ∧ False)) → False)) → ((((p2 ∧ p1) ∨ (p1 → False)) ∧ ((p2 ∨ p4) → False)) → (((p6 ∧ p0) ∧ (p1 → True)) → ((False → False) → (p6 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_2
      case intro assump_17 assump_18 =>
        cases assump_17
        case inl assump_19 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            cases assump_1
            case intro assump_29 assump_30 =>
              apply Or.inl
              exact assump_9
        case inr assump_20 =>
          cases assump_1
          case intro assump_39 assump_40 =>
            apply Or.inl
            exact assump_9


variable (p5 p4 p7 p3 p6 p0 p2 p1 : Prop)
theorem file99_18623 : (((((p1 → p2) ∨ (p6 ∨ False)) ∧ ((p7 → False) ∧ (p3 ∨ p5))) → (((True → False) → (p4 → False)) ∨ ((p3 → False) ∨ (p0 → False)))) ∨ ((((p3 → True) → (p1 → p4)) ∧ ((p0 → p0) → False)) → (((p3 ∧ p0) ∨ (p2 → False)) ∧ ((p1 ∨ p1) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          have assump_74 : True := by
            apply True.intro
          let assump_22 := assump_16 assump_74
          apply False.elim assump_22
        case inr assump_13 =>
          apply Or.inl
          intro assump_28
          intro assump_29
          have assump_75 : True := by
            apply True.intro
          let assump_34 := assump_28 assump_75
          apply False.elim assump_34
    case inr assump_5 =>
      cases assump_5
      case inl assump_38 =>
        cases assump_3
        case intro assump_42 assump_43 =>
          cases assump_43
          case inl assump_46 =>
            apply Or.inl
            intro assump_50
            intro assump_51
            have assump_76 : True := by
              apply True.intro
            let assump_56 := assump_50 assump_76
            apply False.elim assump_56
          case inr assump_47 =>
            apply Or.inl
            intro assump_62
            intro assump_63
            have assump_77 : True := by
              apply True.intro
            let assump_68 := assump_62 assump_77
            apply False.elim assump_68
      case inr assump_39 =>
        apply False.elim assump_39


variable (p1 p6 p0 p4 p5 p2 : Prop)
theorem file99_20419 : ((((((p6 → p5) → (p0 → False)) ∧ ((True → False) ∧ (True ∧ p1))) → False) → ((((p2 ∨ True) ∨ (p6 ∨ p0)) ∨ ((p4 → False) ∧ (p6 ∧ p6))) → False)) → False) := by
  intro assump_1
  have assump_29 : ((((p6 → p5) → (p0 → False)) ∧ ((True → False) ∧ (True ∧ p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_30 : True := by
            apply True.intro
          let assump_21 := assump_10 assump_30
          apply False.elim assump_21
  let assump_4 := assump_1 assump_29
  have assump_31 : (((p2 ∨ True) ∨ (p6 ∨ p0)) ∨ ((p4 → False) ∧ (p6 ∧ p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_25 := assump_4 assump_31
  apply False.elim assump_25


variable (p7 p0 p5 p3 p1 : Prop)
theorem file99_21359 : ((((((p5 ∧ p1) ∧ (False ∧ p7)) → False) ∨ (((p7 ∨ True) ∧ (p3 ∧ p3)) ∧ ((p3 → False) ∨ (True ∨ p3)))) ∧ ((((p0 ∧ False) ∨ (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_197 : (((p0 ∧ False) ∨ (True → False)) → False) := by
        intro assump_11
        cases assump_11
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_13 =>
          have assump_198 : True := by
            apply True.intro
          let assump_22 := assump_13 assump_198
          apply False.elim assump_22
      let assump_10 := assump_3 assump_197
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case inl assump_33 =>
            cases assump_32
            case intro assump_37 assump_38 =>
              cases assump_30
              case inl assump_43 =>
                have assump_199 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                  intro assump_50
                  cases assump_50
                  case inl assump_51 =>
                    cases assump_51
                    case intro assump_53 assump_54 =>
                      apply False.elim assump_54
                  case inr assump_52 =>
                    have assump_200 : True := by
                      apply True.intro
                    let assump_61 := assump_52 assump_200
                    apply False.elim assump_61
                let assump_49 := assump_3 assump_199
                apply False.elim assump_49
              case inr assump_44 =>
                cases assump_44
                case inl assump_68 =>
                  have assump_201 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                    intro assump_75
                    cases assump_75
                    case inl assump_76 =>
                      cases assump_76
                      case intro assump_78 assump_79 =>
                        apply False.elim assump_79
                    case inr assump_77 =>
                      have assump_202 : True := by
                        apply True.intro
                      let assump_86 := assump_77 assump_202
                      apply False.elim assump_86
                  let assump_74 := assump_3 assump_201
                  apply False.elim assump_74
                case inr assump_69 =>
                  have assump_203 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                    intro assump_98
                    cases assump_98
                    case inl assump_99 =>
                      cases assump_99
                      case intro assump_101 assump_102 =>
                        apply False.elim assump_102
                    case inr assump_100 =>
                      have assump_204 : True := by
                        apply True.intro
                      let assump_109 := assump_100 assump_204
                      apply False.elim assump_109
                  let assump_97 := assump_3 assump_203
                  apply False.elim assump_97
          case inr assump_34 =>
            cases assump_32
            case intro assump_118 assump_119 =>
              cases assump_30
              case inl assump_124 =>
                have assump_205 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                  intro assump_131
                  cases assump_131
                  case inl assump_132 =>
                    cases assump_132
                    case intro assump_134 assump_135 =>
                      apply False.elim assump_135
                  case inr assump_133 =>
                    have assump_206 : True := by
                      apply True.intro
                    let assump_142 := assump_133 assump_206
                    apply False.elim assump_142
                let assump_130 := assump_3 assump_205
                apply False.elim assump_130
              case inr assump_125 =>
                cases assump_125
                case inl assump_149 =>
                  have assump_207 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                    intro assump_156
                    cases assump_156
                    case inl assump_157 =>
                      cases assump_157
                      case intro assump_159 assump_160 =>
                        apply False.elim assump_160
                    case inr assump_158 =>
                      have assump_208 : True := by
                        apply True.intro
                      let assump_167 := assump_158 assump_208
                      apply False.elim assump_167
                  let assump_155 := assump_3 assump_207
                  apply False.elim assump_155
                case inr assump_150 =>
                  have assump_209 : (((p0 ∧ False) ∨ (True → False)) → False) := by
                    intro assump_179
                    cases assump_179
                    case inl assump_180 =>
                      cases assump_180
                      case intro assump_182 assump_183 =>
                        apply False.elim assump_183
                    case inr assump_181 =>
                      have assump_210 : True := by
                        apply True.intro
                      let assump_190 := assump_181 assump_210
                      apply False.elim assump_190
                  let assump_178 := assump_3 assump_209
                  apply False.elim assump_178


variable (p4 p3 p0 p2 p7 p1 : Prop)
theorem file99_27144 : (((((p3 ∨ p4) → (p7 → False)) ∧ ((p2 ∧ p1) ∧ (True → False))) → False) ∨ ((((True → False) ∨ (p0 → p0)) ∧ ((False ∧ p0) ∧ (True → False))) → (((p1 ∨ p0) → (p2 → False)) ∨ ((p1 → False) ∧ (p0 → p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_20 : True := by
          apply True.intro
        let assump_16 := assump_7 assump_20
        apply False.elim assump_16


variable (p3 p4 p0 p1 p7 : Prop)
theorem file99_27747 : (((((False ∨ True) ∨ (p1 → p1)) → ((p3 → True) → False)) → False) ∨ ((((True ∧ p7) ∨ (p3 ∧ p4)) → ((p0 ∨ p4) → False)) → (((p7 ∨ p7) ∧ (p0 ∨ True)) ∧ ((False ∧ p0) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_10 : ((False ∨ True) ∨ (p1 → p1)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_10
  have assump_11 : (p3 → True) := by
    intro assump_6
    apply True.intro
  let assump_5 := assump_4 assump_11
  apply False.elim assump_5


variable (p7 p3 p0 p5 p2 p4 p1 p6 : Prop)
theorem file99_28322 : (((((p1 → False) → False) ∨ ((p5 → p5) → False)) → (((p1 ∧ p4) ∨ (p4 ∧ True)) ∨ ((p2 → p6) → (p4 → True)))) ∨ ((((p7 ∧ p2) → (p3 ∨ p7)) ∨ ((p0 ∨ p0) ∨ (p1 → False))) ∨ (((p1 ∨ p4) → False) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_25
  cases assump_25
  case inl assump_26 =>
    apply Or.inr
    intro assump_30
    intro assump_31
    apply True.intro
  case inr assump_27 =>
    apply Or.inr
    intro assump_34
    intro assump_35
    apply True.intro


variable (p4 p7 p6 p2 p1 : Prop)
theorem file99_28857 : (((((p7 ∨ False) ∧ (p7 ∧ p4)) → False) ∧ (((p6 → p2) → False) ∨ ((p2 → False) ∨ (p1 ∧ p2)))) → ((((True → False) ∨ (p6 → p4)) ∧ ((p4 → False) ∧ (False → False))) → (((p7 ∨ p1) ∨ (p6 ∨ p6)) ∨ ((True ∨ p2) ∨ (False → True))))) := by
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      cases assump_14
      case intro assump_19 assump_20 =>
        cases assump_11
        case intro assump_25 assump_26 =>
          cases assump_26
          case inl assump_29 =>
            apply Or.inr
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_30 =>
            cases assump_30
            case inl assump_33 =>
              apply Or.inr
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_34 =>
              cases assump_34
              case intro assump_37 assump_38 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_37
    case inr assump_16 =>
      cases assump_14
      case intro assump_45 assump_46 =>
        cases assump_11
        case intro assump_51 assump_52 =>
          cases assump_52
          case inl assump_55 =>
            apply Or.inr
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_56 =>
            cases assump_56
            case inl assump_59 =>
              apply Or.inr
              apply Or.inl
              apply Or.inl
              apply True.intro
            case inr assump_60 =>
              cases assump_60
              case intro assump_63 assump_64 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_63


variable (p4 p7 p1 p6 p3 p2 p0 p5 : Prop)
theorem file99_30770 : (((((True ∨ p4) ∨ (p0 ∨ p2)) ∨ ((False ∨ p0) → (p6 → False))) → False) → ((((p1 ∧ p7) ∨ (p5 → True)) ∧ ((p1 ∨ p3) ∨ (p5 → False))) ∧ (((p4 → False) → (True ∨ p0)) ∧ ((p6 ∧ p6) → (p1 ∧ p1))))) := by
  intro assump_13
  apply And.intro
  apply And.intro
  apply Or.inr
  intro assump_16
  apply True.intro
  apply Or.inr
  intro assump_19
  have assump_57 : (((True ∨ p4) ∨ (p0 ∨ p2)) ∨ ((False ∨ p0) → (p6 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_23 := assump_13 assump_57
  apply False.elim assump_23
  apply And.intro
  intro assump_27
  apply Or.inl
  apply True.intro
  intro assump_32
  apply And.intro
  cases assump_32
  case intro assump_33 assump_34 =>
    have assump_58 : (((True ∨ p4) ∨ (p0 ∨ p2)) ∨ ((False ∨ p0) → (p6 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_41 := assump_13 assump_58
    apply False.elim assump_41
  cases assump_32
  case intro assump_45 assump_46 =>
    have assump_59 : (((True ∨ p4) ∨ (p0 ∨ p2)) ∨ ((False ∨ p0) → (p6 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_53 := assump_13 assump_59
    apply False.elim assump_53


variable (p6 p3 p0 p5 : Prop)
theorem file99_32078 : ((((((p6 → False) → (p0 → True)) → False) → (((True ∧ p0) ∧ (p6 → True)) → ((p6 ∨ p5) ∨ (p6 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 → False) → (p0 → True)) → False) → (((True ∧ p0) ∧ (p6 → True)) → ((p6 ∨ p5) ∨ (p6 ∧ p3)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_29 : ((p6 → False) → (p0 → True)) := by
          intro assump_20
          intro assump_21
          apply True.intro
        let assump_19 := assump_5 assump_29
        apply False.elim assump_19
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p7 p6 p5 p3 p0 p1 p4 p2 : Prop)
theorem file99_32846 : ((((((p6 ∨ p1) → (p5 ∧ True)) → ((p0 ∨ True) ∨ (p2 → p5))) → False) ∧ ((((p3 ∨ p1) ∧ (False ∧ p0)) → ((False → p5) → False)) ∨ (((p6 ∨ p2) → (p2 ∨ p6)) ∧ ((p7 → p4) ∨ (p5 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_46 : (((p6 ∨ p1) → (p5 ∧ True)) → ((p0 ∨ True) ∨ (p2 → p5))) := by
        intro assump_12
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_11 := assump_2 assump_46
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          have assump_47 : (((p6 ∨ p1) → (p5 ∧ True)) → ((p0 ∨ True) ∨ (p2 → p5))) := by
            intro assump_29
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_28 := assump_2 assump_47
          apply False.elim assump_28
        case inr assump_23 =>
          have assump_48 : (((p6 ∨ p1) → (p5 ∧ True)) → ((p0 ∨ True) ∨ (p2 → p5))) := by
            intro assump_40
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_39 := assump_2 assump_48
          apply False.elim assump_39


variable (p6 p7 p1 p5 : Prop)
theorem file99_34187 : ((((((False ∨ p7) → (p7 ∨ p6)) → False) → (((p5 ∨ p1) ∧ (p1 ∨ p5)) → ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_85 : ((((False ∨ p7) → (p7 ∨ p6)) → False) → (((p5 ∨ p1) ∧ (p1 ∨ p5)) → ((True → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case inl assump_16 =>
          have assump_86 : ((False ∨ p7) → (p7 ∨ p6)) := by
            intro assump_23
            cases assump_23
            case inl assump_24 =>
              apply False.elim assump_24
            case inr assump_25 =>
              apply Or.inl
              exact assump_25
          let assump_22 := assump_5 assump_86
          apply False.elim assump_22
        case inr assump_17 =>
          have assump_87 : ((False ∨ p7) → (p7 ∨ p6)) := by
            intro assump_38
            cases assump_38
            case inl assump_39 =>
              apply False.elim assump_39
            case inr assump_40 =>
              apply Or.inl
              exact assump_40
          let assump_37 := assump_5 assump_87
          apply False.elim assump_37
      case inr assump_13 =>
        cases assump_11
        case inl assump_50 =>
          have assump_88 : ((False ∨ p7) → (p7 ∨ p6)) := by
            intro assump_57
            cases assump_57
            case inl assump_58 =>
              apply False.elim assump_58
            case inr assump_59 =>
              apply Or.inl
              exact assump_59
          let assump_56 := assump_5 assump_88
          apply False.elim assump_56
        case inr assump_51 =>
          have assump_89 : ((False ∨ p7) → (p7 ∨ p6)) := by
            intro assump_72
            cases assump_72
            case inl assump_73 =>
              apply False.elim assump_73
            case inr assump_74 =>
              apply Or.inl
              exact assump_74
          let assump_71 := assump_5 assump_89
          apply False.elim assump_71
  let assump_4 := assump_1 assump_85
  apply False.elim assump_4


variable (p0 p7 p3 p5 : Prop)
theorem file99_36382 : (((((p3 ∨ p7) ∧ (p5 ∨ p0)) → False) ∧ (((True ∧ True) → False) ∧ ((p0 ∧ False) → (p0 ∧ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : (True ∧ True) := by
        apply And.intro
        apply True.intro
        apply True.intro
      let assump_13 := assump_6 assump_17
      apply False.elim assump_13


variable (p3 p1 p6 p0 p7 : Prop)
theorem file99_36863 : (((((False → False) ∨ (p1 ∧ p6)) ∨ ((True ∨ p7) ∧ (False → p7))) ∨ (((p1 → False) ∨ (True → False)) ∨ ((p3 → True) → (p0 ∧ p6)))) → ((((p0 ∧ True) ∨ (p0 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_141 : ((p0 ∧ True) ∨ (p0 → False)) := by
          apply Or.inr
          intro assump_15
          have assump_142 : ((p0 ∧ True) ∨ (p0 → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_15
            apply True.intro
          let assump_20 := assump_2 assump_142
          apply False.elim assump_20
        let assump_14 := assump_2 assump_141
        apply False.elim assump_14
      case inr assump_10 =>
        cases assump_10
        case intro assump_27 assump_28 =>
          have assump_143 : ((p0 ∧ True) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_36
            have assump_144 : ((p0 ∧ True) ∨ (p0 → False)) := by
              apply Or.inl
              apply And.intro
              exact assump_36
              apply True.intro
            let assump_42 := assump_2 assump_144
            apply False.elim assump_42
          let assump_35 := assump_2 assump_143
          apply False.elim assump_35
    case inr assump_8 =>
      cases assump_8
      case intro assump_49 assump_50 =>
        cases assump_49
        case inl assump_51 =>
          have assump_145 : ((p0 ∧ True) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_59
            have assump_146 : ((p0 ∧ True) ∨ (p0 → False)) := by
              apply Or.inl
              apply And.intro
              exact assump_59
              apply True.intro
            let assump_64 := assump_2 assump_146
            apply False.elim assump_64
          let assump_58 := assump_2 assump_145
          apply False.elim assump_58
        case inr assump_52 =>
          have assump_147 : ((p0 ∧ True) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_78
            have assump_148 : ((p0 ∧ True) ∨ (p0 → False)) := by
              apply Or.inl
              apply And.intro
              exact assump_78
              apply True.intro
            let assump_84 := assump_2 assump_148
            apply False.elim assump_84
          let assump_77 := assump_2 assump_147
          apply False.elim assump_77
  case inr assump_6 =>
    cases assump_6
    case inl assump_91 =>
      cases assump_91
      case inl assump_93 =>
        have assump_149 : ((p0 ∧ True) ∨ (p0 → False)) := by
          apply Or.inr
          intro assump_99
          have assump_150 : ((p0 ∧ True) ∨ (p0 → False)) := by
            apply Or.inl
            apply And.intro
            exact assump_99
            apply True.intro
          let assump_104 := assump_2 assump_150
          apply False.elim assump_104
        let assump_98 := assump_2 assump_149
        apply False.elim assump_98
      case inr assump_94 =>
        have assump_151 : True := by
          apply True.intro
        let assump_113 := assump_94 assump_151
        apply False.elim assump_113
    case inr assump_92 =>
      have assump_152 : ((p0 ∧ True) ∨ (p0 → False)) := by
        apply Or.inr
        intro assump_125
        have assump_153 : ((p0 ∧ True) ∨ (p0 → False)) := by
          apply Or.inl
          apply And.intro
          exact assump_125
          apply True.intro
        let assump_134 := assump_2 assump_153
        apply False.elim assump_134
      let assump_124 := assump_2 assump_152
      apply False.elim assump_124


variable (p3 p0 p6 p1 p7 p5 p4 p2 : Prop)
theorem file99_40604 : ((((((p3 ∨ p2) ∧ (True ∨ p1)) → ((True ∨ p4) → False)) ∧ (((p5 → False) ∨ (True → False)) → False)) ∧ ((((False → p5) ∧ (True → False)) ∧ ((p2 ∧ p7) ∧ (False → p0))) ∧ (((p0 ∧ p4) → (p0 ∨ p6)) ∨ ((p5 ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_11
                case inl assump_30 =>
                  have assump_52 : True := by
                    apply True.intro
                  let assump_38 := assump_15 assump_52
                  apply False.elim assump_38
                case inr assump_31 =>
                  have assump_53 : True := by
                    apply True.intro
                  let assump_48 := assump_15 assump_53
                  apply False.elim assump_48


variable (p0 p1 p7 p5 p4 p3 p2 : Prop)
theorem file99_41846 : (((((p1 → False) ∧ (p0 ∧ False)) → ((True → False) ∧ (p3 → False))) ∨ (((p2 → False) → False) ∧ ((p1 ∧ p5) → False))) ∨ ((((p7 ∨ False) → (p3 ∧ p2)) ∨ ((p7 → False) ∧ (True ∨ p4))) ∧ (((p3 ∨ p2) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  intro assump_15
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      apply False.elim assump_23


variable (p6 p2 p4 p3 p7 p5 p1 p0 : Prop)
theorem file99_42517 : ((((((p4 → False) → False) ∧ ((p1 ∨ p6) ∨ (p2 → p0))) → False) ∧ ((((p7 → p5) → (p2 ∨ True)) → False) ∧ (((p4 ∨ p5) → (p7 ∨ p3)) ∧ ((p1 ∨ p7) → False)))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        have assump_31 : ((p7 → p5) → (p2 ∨ True)) := by
          intro assump_25
          apply Or.inr
          apply True.intro
        let assump_24 := assump_12 assump_31
        apply False.elim assump_24


variable (p4 p7 p1 p6 p2 : Prop)
theorem file99_43143 : ((((((p7 ∨ p6) → False) ∨ ((p1 → False) ∨ (p2 → p1))) → (((True → False) → (True → False)) ∨ ((p4 ∧ p4) → (p2 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p7 ∨ p6) → False) ∨ ((p1 → False) ∨ (p2 → p1))) → (((True → False) → (True → False)) ∨ ((p4 ∧ p4) → (p2 ∧ p1)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      have assump_50 : True := by
        apply True.intro
      let assump_16 := assump_10 assump_50
      apply False.elim assump_16
    case inr assump_7 =>
      cases assump_7
      case inl assump_20 =>
        apply Or.inl
        intro assump_24
        intro assump_25
        have assump_51 : True := by
          apply True.intro
        let assump_30 := assump_24 assump_51
        apply False.elim assump_30
      case inr assump_21 =>
        apply Or.inl
        intro assump_36
        intro assump_37
        have assump_52 : True := by
          apply True.intro
        let assump_42 := assump_36 assump_52
        apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p5 p0 p3 p2 : Prop)
theorem file99_44351 : ((((((p5 ∨ False) → (p0 ∧ p3)) → ((True ∨ p5) ∨ (p5 → p2))) ∨ (((p5 → False) → False) ∧ ((p0 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p5 ∨ False) → (p0 ∧ p3)) → ((True ∨ p5) ∨ (p5 → p2))) ∨ (((p5 → False) → False) ∧ ((p0 ∧ False) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p1 p4 p7 : Prop)
theorem file99_44851 : ((((((p7 ∨ p2) → False) ∧ ((p7 ∧ p4) → False)) ∨ (((False ∧ p7) ∨ (p7 ∧ p1)) → False)) ∧ ((((p4 → p4) → (p2 → p2)) ∨ ((True ∧ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_38 : (((p4 → p4) → (p2 → p2)) ∨ ((True ∧ p2) → False)) := by
          apply Or.inl
          intro assump_15
          intro assump_16
          exact assump_16
        let assump_14 := assump_3 assump_38
        apply False.elim assump_14
    case inr assump_5 =>
      have assump_39 : (((p4 → p4) → (p2 → p2)) ∨ ((True ∧ p2) → False)) := by
        apply Or.inl
        intro assump_29
        intro assump_30
        exact assump_30
      let assump_28 := assump_3 assump_39
      apply False.elim assump_28


variable (p2 p0 p6 : Prop)
theorem file99_45771 : ((((((False ∨ p2) → (p0 ∧ True)) → False) → (((p6 → False) → False) → ((p0 ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((False ∨ p2) → (p0 ∧ True)) → False) → (((p6 → False) → False) → ((p0 ∨ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      have assump_33 : ((False ∨ p2) → (p0 ∧ True)) := by
        intro assump_17
        apply And.intro
        cases assump_17
        case inl assump_18 =>
          apply False.elim assump_18
        case inr assump_19 =>
          exact assump_8
        apply True.intro
      let assump_16 := assump_5 assump_33
      apply False.elim assump_16
    case inr assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p5 p2 p3 : Prop)
theorem file99_46651 : ((((((True → False) ∧ (p2 → False)) → ((False → False) ∨ (p5 ∧ p3))) ∨ (((True → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) ∧ (p2 → False)) → ((False → False) ∨ (p5 ∧ p3))) ∨ (((True → False) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p5 p1 p4 p7 p6 p3 : Prop)
theorem file99_47222 : (((((False ∧ p7) ∧ (p5 → False)) → False) ∨ (((p5 → False) ∧ (False → p6)) → False)) ∨ ((((p3 → p2) ∧ (p1 → False)) ∨ ((False ∧ False) ∧ (p4 → False))) ∧ (((p4 → False) → False) → ((p7 → False) ∨ (p2 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p4 p0 p5 p1 p6 p2 p7 : Prop)
theorem file99_47689 : (((((p6 ∧ p5) ∨ (False ∨ p7)) ∨ ((False → p6) ∨ (p7 ∨ p6))) ∨ (((p7 → p0) ∨ (True → False)) → False)) ∨ ((((p1 ∧ p7) → False) ∨ ((p7 ∨ p6) ∧ (p2 → False))) → (((p0 → p0) → (False ∧ p1)) ∧ ((p2 → p6) → (p7 → p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p0 p4 p6 p3 p1 p7 p5 : Prop)
theorem file99_48078 : ((((((False ∨ p3) ∨ (False → False)) → False) → (((p0 ∧ p6) ∨ (p0 ∧ p1)) → ((p3 ∧ p7) ∧ (p4 ∧ False)))) ∧ ((((p5 ∨ p0) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p5 ∨ p0) ∧ (True → False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_34 : True := by
            apply True.intro
          let assump_18 := assump_11 assump_34
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_35 : True := by
            apply True.intro
          let assump_26 := assump_11 assump_35
          apply False.elim assump_26
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p6 p4 p5 p0 p1 p2 : Prop)
theorem file99_48980 : (((((p2 → False) ∧ (p6 ∨ p1)) ∧ ((p4 ∧ True) ∧ (p6 ∧ p2))) → (((False → False) ∨ (p1 → p6)) ∧ ((p0 → False) ∨ (False ∧ p2)))) ∧ ((((False → p6) → False) ∧ ((p6 ∧ p6) → (p5 ∧ p2))) → False)) := by
  apply And.intro
  intro assump_14
  apply And.intro
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case inl assump_21 =>
        cases assump_16
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_26
            case intro assump_33 assump_34 =>
              apply Or.inl
              intro assump_39
              apply False.elim assump_39
      case inr assump_22 =>
        cases assump_16
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            cases assump_45
            case intro assump_52 assump_53 =>
              apply Or.inl
              intro assump_58
              apply False.elim assump_58
  cases assump_14
  case intro assump_61 assump_62 =>
    cases assump_61
    case intro assump_63 assump_64 =>
      cases assump_64
      case inl assump_67 =>
        cases assump_62
        case intro assump_71 assump_72 =>
          cases assump_71
          case intro assump_73 assump_74 =>
            cases assump_72
            case intro assump_79 assump_80 =>
              apply Or.inl
              intro assump_85
              have assump_140 : p2 := by
                exact assump_80
              let assump_93 := assump_63 assump_140
              apply False.elim assump_93
      case inr assump_68 =>
        cases assump_62
        case intro assump_99 assump_100 =>
          cases assump_99
          case intro assump_101 assump_102 =>
            cases assump_100
            case intro assump_107 assump_108 =>
              apply Or.inl
              intro assump_113
              have assump_141 : p2 := by
                exact assump_108
              let assump_121 := assump_63 assump_141
              apply False.elim assump_121
  intro assump_125
  cases assump_125
  case intro assump_126 assump_127 =>
    have assump_142 : (False → p6) := by
      intro assump_134
      apply False.elim assump_134
    let assump_133 := assump_126 assump_142
    apply False.elim assump_133


variable (p0 p4 p2 p6 p1 : Prop)
theorem file99_51409 : ((((((p2 ∧ p0) → False) ∧ ((p1 → False) ∧ (False ∧ p6))) ∧ (((p6 ∧ p1) → False) → ((p4 ∨ p6) ∧ (False ∧ p4)))) ∧ ((((p0 → p4) → False) ∧ ((True ∧ p0) → (p1 → False))) → False)) → False) := by
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


variable (p1 p6 p4 p0 p3 p2 p5 : Prop)
theorem file99_52020 : (((((True → False) ∧ (p3 → p4)) → ((p6 → False) ∧ (p0 → False))) ∨ (((True ∧ p1) → (p5 ∧ p3)) ∨ ((True ∧ p2) ∨ (p6 → False)))) ∨ ((((p5 ∨ p0) → (p2 → False)) ∨ ((p5 → True) ∧ (p6 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    have assump_34 : True := by
      apply True.intro
    let assump_16 := assump_9 assump_34
    apply False.elim assump_16
  intro assump_20
  cases assump_5
  case intro assump_23 assump_24 =>
    have assump_35 : True := by
      apply True.intro
    let assump_30 := assump_23 assump_35
    apply False.elim assump_30


variable (p6 p0 p1 p4 p7 p5 p3 : Prop)
theorem file99_52747 : (((((p5 ∨ p0) → False) ∧ ((p3 → False) ∧ (p3 ∨ p3))) → False) ∨ ((((p6 → p0) ∨ (p3 → False)) ∨ ((p3 ∨ p4) ∧ (p1 → p4))) ∧ (((False ∧ p6) ∧ (p5 → p7)) ∧ ((p6 ∧ True) → (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_26 : p3 := by
          exact assump_10
        let assump_15 := assump_6 assump_26
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_27 : p3 := by
          exact assump_11
        let assump_22 := assump_6 assump_27
        apply False.elim assump_22


variable (p5 p4 p1 p7 p0 : Prop)
theorem file99_53487 : (((((p5 ∧ False) → (p0 → False)) ∧ ((True → False) ∧ (p4 ∧ True))) ∧ (((p0 ∧ p7) ∨ (p5 ∨ p0)) → ((p1 ∨ p7) → (p5 ∨ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_26 : True := by
            apply True.intro
          let assump_22 := assump_8 assump_26
          apply False.elim assump_22


variable (p6 p4 p2 p7 : Prop)
theorem file99_54075 : ((((((False → False) ∧ (True → False)) → False) ∨ (((p4 → False) → False) → ((p6 ∧ p7) ∨ (True ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) ∧ (True → False)) → False) ∨ (((p4 → False) → False) → ((p6 ∧ p7) ∨ (True ∨ p2)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p5 p2 p0 p4 p1 p6 p3 : Prop)
theorem file99_54703 : (((((p3 ∧ p3) ∨ (p3 → False)) ∨ ((p7 ∧ p0) → (p7 → p2))) → False) → ((((p6 ∨ p4) ∧ (p7 ∨ True)) → ((p5 → False) ∧ (p0 ∧ p0))) → (((False → False) → (p1 ∧ p3)) → ((p0 → False) ∧ (p3 → p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  have assump_38 : (((p3 ∧ p3) ∨ (p3 → False)) ∨ ((p7 ∧ p0) → (p7 → p2))) := by
    apply Or.inl
    apply Or.inr
    intro assump_14
    have assump_39 : (((p3 ∧ p3) ∨ (p3 → False)) ∨ ((p7 ∧ p0) → (p7 → p2))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_14
      exact assump_14
    let assump_18 := assump_1 assump_39
    apply False.elim assump_18
  let assump_13 := assump_1 assump_38
  apply False.elim assump_13
  intro assump_25
  have assump_40 : (((p3 ∧ p3) ∨ (p3 → False)) ∨ ((p7 ∧ p0) → (p7 → p2))) := by
    apply Or.inl
    apply Or.inl
    apply And.intro
    exact assump_25
    exact assump_25
  let assump_34 := assump_1 assump_40
  apply False.elim assump_34


variable (p4 p3 p5 p6 p0 p7 p1 : Prop)
theorem file99_55766 : ((((((p4 → False) ∧ (p7 → False)) ∨ ((True → p5) ∨ (p4 → False))) ∧ (((p0 ∧ p1) ∨ (False ∨ False)) ∧ ((p3 → True) → False))) ∧ ((((p0 ∧ p0) → False) ∧ ((p5 → p6) ∧ (False ∧ p6))) ∨ (((True ∨ p5) ∧ (p1 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_3
                case inl assump_26 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_29
                    case intro assump_32 assump_33 =>
                      cases assump_33
                      case intro assump_36 assump_37 =>
                        apply False.elim assump_36
                case inr assump_27 =>
                  have assump_143 : ((True ∨ p5) ∧ (p1 → p1)) := by
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    intro assump_43
                    exact assump_43
                  let assump_42 := assump_27 assump_143
                  apply False.elim assump_42
            case inr assump_17 =>
              cases assump_17
              case inl assump_49 =>
                apply False.elim assump_49
              case inr assump_50 =>
                apply False.elim assump_50
      case inr assump_7 =>
        cases assump_7
        case inl assump_55 =>
          cases assump_5
          case intro assump_59 assump_60 =>
            cases assump_59
            case inl assump_61 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_3
                case inl assump_71 =>
                  cases assump_71
                  case intro assump_73 assump_74 =>
                    cases assump_74
                    case intro assump_77 assump_78 =>
                      cases assump_78
                      case intro assump_81 assump_82 =>
                        apply False.elim assump_81
                case inr assump_72 =>
                  have assump_144 : ((True ∨ p5) ∧ (p1 → p1)) := by
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    intro assump_88
                    exact assump_88
                  let assump_87 := assump_72 assump_144
                  apply False.elim assump_87
            case inr assump_62 =>
              cases assump_62
              case inl assump_94 =>
                apply False.elim assump_94
              case inr assump_95 =>
                apply False.elim assump_95
        case inr assump_56 =>
          cases assump_5
          case intro assump_102 assump_103 =>
            cases assump_102
            case inl assump_104 =>
              cases assump_104
              case intro assump_106 assump_107 =>
                cases assump_3
                case inl assump_114 =>
                  cases assump_114
                  case intro assump_116 assump_117 =>
                    cases assump_117
                    case intro assump_120 assump_121 =>
                      cases assump_121
                      case intro assump_124 assump_125 =>
                        apply False.elim assump_124
                case inr assump_115 =>
                  have assump_145 : ((True ∨ p5) ∧ (p1 → p1)) := by
                    apply And.intro
                    apply Or.inl
                    apply True.intro
                    intro assump_131
                    exact assump_131
                  let assump_130 := assump_115 assump_145
                  apply False.elim assump_130
            case inr assump_105 =>
              cases assump_105
              case inl assump_137 =>
                apply False.elim assump_137
              case inr assump_138 =>
                apply False.elim assump_138


variable (p6 p4 p1 p0 p2 p3 : Prop)
theorem file99_60052 : ((((((p4 ∧ p3) ∨ (p0 ∨ True)) → ((True → p6) → (p6 ∨ p2))) → False) ∧ ((((False → True) → False) ∧ ((p2 ∨ p6) ∧ (p4 → p1))) ∧ (((p0 ∨ False) → False) ∨ ((True ∧ p2) → False)))) → False) := by
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
            cases assump_7
            case inl assump_20 =>
              have assump_64 : (False → True) := by
                intro assump_28
                apply True.intro
              let assump_27 := assump_8 assump_64
              apply False.elim assump_27
            case inr assump_21 =>
              have assump_65 : (True ∧ p2) := by
                apply And.intro
                apply True.intro
                exact assump_14
              let assump_34 := assump_21 assump_65
              apply False.elim assump_34
          case inr assump_15 =>
            cases assump_7
            case inl assump_42 =>
              have assump_66 : (False → True) := by
                intro assump_50
                apply True.intro
              let assump_49 := assump_8 assump_66
              apply False.elim assump_49
            case inr assump_43 =>
              have assump_67 : (False → True) := by
                intro assump_60
                apply True.intro
              let assump_59 := assump_8 assump_67
              apply False.elim assump_59


variable (p2 p5 p0 p3 : Prop)
theorem file99_61687 : (((((p5 → p5) → (p2 → False)) ∧ ((True ∨ p5) → False)) → False) → ((((False ∧ p5) → False) ∨ ((False ∨ p3) → False)) ∨ (((p0 ∨ p2) → (p5 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p3 p1 p6 p0 p4 : Prop)
theorem file99_62053 : (((((p3 ∨ True) → False) → False) → False) → ((((p6 ∨ p0) → (p4 → False)) ∨ ((p1 → p3) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_35 : (((p3 ∨ True) → False) → False) := by
      intro assump_10
      have assump_36 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_13 := assump_10 assump_36
      apply False.elim assump_13
    let assump_9 := assump_1 assump_35
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_37 : (((p3 ∨ True) → False) → False) := by
      intro assump_25
      have assump_38 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_28 := assump_25 assump_38
      apply False.elim assump_28
    let assump_24 := assump_1 assump_37
    apply False.elim assump_24


variable (p6 p2 p1 p0 p7 p5 p3 : Prop)
theorem file99_62954 : ((((((p1 → p0) → False) → False) → False) ∧ ((((p2 → False) ∧ (p7 ∨ p5)) ∧ ((p7 ∧ p2) ∧ (p6 ∨ True))) ∧ (((p0 ∧ p1) ∨ (p3 ∧ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case inl assump_26 =>
                  have assump_90 : p2 := by
                    exact assump_21
                  let assump_37 := assump_10 assump_90
                  apply False.elim assump_37
                case inr assump_27 =>
                  have assump_91 : p2 := by
                    exact assump_21
                  let assump_49 := assump_10 assump_91
                  apply False.elim assump_49
          case inr assump_15 =>
            cases assump_9
            case intro assump_55 assump_56 =>
              cases assump_55
              case intro assump_57 assump_58 =>
                cases assump_56
                case inl assump_63 =>
                  have assump_92 : p2 := by
                    exact assump_58
                  let assump_74 := assump_10 assump_92
                  apply False.elim assump_74
                case inr assump_64 =>
                  have assump_93 : p2 := by
                    exact assump_58
                  let assump_86 := assump_10 assump_93
                  apply False.elim assump_86


variable (p6 p0 p7 p5 p4 p2 p1 : Prop)
theorem file99_64747 : (((((p7 → p2) ∧ (p5 ∧ False)) → ((True → False) ∧ (p2 → p2))) ∧ (((True → False) → False) ∨ ((p4 → False) → False))) ∨ ((((p0 → False) ∨ (p1 → False)) ∨ ((p4 ∧ p6) → (p1 ∧ True))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  intro assump_15
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      apply False.elim assump_23
  apply Or.inl
  intro assump_28
  have assump_35 : True := by
    apply True.intro
  let assump_31 := assump_28 assump_35
  apply False.elim assump_31


variable (p0 p4 p3 p6 p2 : Prop)
theorem file99_65539 : ((((((p2 → p0) ∧ (p3 → p4)) → ((p6 ∧ True) → False)) ∧ (((p3 → False) → False) → ((p4 ∨ p2) ∧ (p3 ∧ p2)))) ∧ ((((p4 ∧ p3) ∨ (True ∧ p4)) → ((False → False) ∨ (True ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_37 : (((p4 ∧ p3) ∨ (True ∧ p4)) → ((False → False) ∨ (True ∨ True))) := by
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            apply False.elim assump_22
        case inr assump_15 =>
          cases assump_15
          case intro assump_25 assump_26 =>
            apply Or.inl
            intro assump_31
            apply False.elim assump_31
      let assump_12 := assump_3 assump_37
      apply False.elim assump_12


variable (p5 p7 p4 p3 p0 p1 p6 p2 : Prop)
theorem file99_66527 : (((((p1 → p1) ∨ (p7 ∧ p3)) ∧ ((p3 ∨ p2) ∧ (p7 → p5))) ∧ (((p4 ∨ p0) ∨ (p0 ∧ p6)) → False)) ∨ ((((False ∧ p6) ∨ (True ∧ p4)) ∨ ((p0 ∨ p3) → (False → True))) ∨ (((p3 → p3) ∨ (p7 → False)) → False))) := by
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  apply True.intro


variable (p2 p7 p1 p3 p4 : Prop)
theorem file99_66885 : ((((((p2 ∧ False) → False) → False) ∧ (((p4 → False) → False) ∧ ((p1 → p2) ∧ (p4 → False)))) ∧ ((((False ∧ False) → (p4 → False)) ∨ ((p7 ∧ p4) ∧ (p3 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_32 : (((False ∧ False) → (p4 → False)) ∨ ((p7 ∧ p4) ∧ (p3 → p4))) := by
            apply Or.inl
            intro assump_21
            intro assump_22
            cases assump_21
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
          let assump_20 := assump_3 assump_32
          apply False.elim assump_20


variable (p1 p6 p5 p0 p2 p7 p3 p4 : Prop)
theorem file99_67753 : (((((False ∧ p1) ∧ (p5 ∨ p0)) → ((p6 → True) ∨ (p2 ∧ p5))) ∧ (((p4 ∧ True) ∨ (p0 ∧ True)) → ((True → False) → (p0 ∧ p7)))) → ((((p5 ∨ True) → False) → False) ∨ (((p1 → p5) ∧ (False → p2)) ∧ ((True ∧ p3) → False)))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    intro assump_12
    have assump_19 : (p5 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_15 := assump_12 assump_19
    apply False.elim assump_15


variable (p6 p3 p1 p7 p2 : Prop)
theorem file99_68289 : ((((((p7 ∧ p7) ∧ (p6 → True)) ∧ ((p7 ∨ p1) → False)) → False) → ((((p2 ∧ p2) → (p2 ∨ p1)) ∨ ((False → p1) → False)) → (((p3 ∨ p7) ∨ (p3 → False)) → False))) → False) := by
  intro assump_1
  have assump_72 : ((((p7 ∧ p7) ∧ (p6 → True)) ∧ ((p7 ∨ p1) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_73 : (p7 ∨ p1) := by
            apply Or.inl
            exact assump_11
          let assump_20 := assump_7 assump_73
          apply False.elim assump_20
  let assump_4 := assump_1 assump_72
  have assump_74 : (((p2 ∧ p2) → (p2 ∨ p1)) ∨ ((False → p1) → False)) := by
    apply Or.inl
    intro assump_25
    cases assump_25
    case intro assump_26 assump_27 =>
      apply Or.inl
      exact assump_27
  let assump_24 := assump_4 assump_74
  have assump_75 : ((p3 ∨ p7) ∨ (p3 → False)) := by
    apply Or.inr
    intro assump_33
    have assump_76 : ((((p7 ∧ p7) ∧ (p6 → True)) ∧ ((p7 ∨ p1) → False)) → False) := by
      intro assump_38
      cases assump_38
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            have assump_77 : (p7 ∨ p1) := by
              apply Or.inl
              exact assump_44
            let assump_53 := assump_40 assump_77
            apply False.elim assump_53
    let assump_37 := assump_1 assump_76
    have assump_78 : (((p2 ∧ p2) → (p2 ∨ p1)) ∨ ((False → p1) → False)) := by
      apply Or.inl
      intro assump_58
      cases assump_58
      case intro assump_59 assump_60 =>
        apply Or.inl
        exact assump_60
    let assump_57 := assump_37 assump_78
    have assump_79 : ((p3 ∨ p7) ∨ (p3 → False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_33
    let assump_65 := assump_57 assump_79
    apply False.elim assump_65
  let assump_32 := assump_24 assump_75
  apply False.elim assump_32


variable (p3 p7 p5 p1 p2 p0 p4 p6 : Prop)
theorem file99_70440 : (((((p4 → p3) ∧ (p1 ∧ p6)) ∨ ((p6 → p7) → (p4 → p3))) ∨ (((p2 ∧ p5) → (True → False)) → False)) → ((((False ∧ p7) → (p7 ∨ True)) → ((p5 → False) → (p1 ∨ True))) ∨ (((p1 ∨ True) → False) ∨ ((True ∧ p3) ∨ (p0 ∨ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          apply Or.inl
          exact assump_10
    case inr assump_5 =>
      apply Or.inl
      intro assump_24
      intro assump_25
      apply Or.inr
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_32
    intro assump_33
    apply Or.inr
    apply True.intro


variable (p4 p0 p1 p3 p7 p6 : Prop)
theorem file99_71323 : ((((((False ∨ p4) → (p3 → False)) → ((p0 → p0) → (p3 → p6))) ∧ (((p0 → False) → False) ∧ ((p1 → p1) ∨ (p0 ∨ p7)))) ∧ ((((False ∧ p0) ∧ (False → False)) → ((p0 ∨ True) ∧ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_70 : (((False ∧ p0) ∧ (False → False)) → ((p0 ∨ True) ∧ (False → False))) := by
            intro assump_19
            apply And.intro
            cases assump_19
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_22
            intro assump_26
            apply False.elim assump_26
          let assump_18 := assump_3 assump_70
          apply False.elim assump_18
        case inr assump_13 =>
          cases assump_13
          case inl assump_32 =>
            have assump_71 : (((False ∧ p0) ∧ (False → False)) → ((p0 ∨ True) ∧ (False → False))) := by
              intro assump_39
              apply And.intro
              cases assump_39
              case intro assump_40 assump_41 =>
                cases assump_40
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42
              intro assump_46
              apply False.elim assump_46
            let assump_38 := assump_3 assump_71
            apply False.elim assump_38
          case inr assump_33 =>
            have assump_72 : (((False ∧ p0) ∧ (False → False)) → ((p0 ∨ True) ∧ (False → False))) := by
              intro assump_57
              apply And.intro
              cases assump_57
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  apply False.elim assump_60
              intro assump_64
              apply False.elim assump_64
            let assump_56 := assump_3 assump_72
            apply False.elim assump_56


variable (p3 p1 p5 p0 p6 p7 p4 : Prop)
theorem file99_73510 : (((((p5 → False) ∧ (False ∨ p4)) → False) ∨ (((p4 → p4) ∨ (p6 ∨ p0)) → False)) → ((((p5 → False) ∧ (p3 ∧ p7)) ∨ ((p0 ∨ False) ∧ (p6 → p5))) → (((p1 ∧ p4) ∨ (p0 ∨ p0)) ∨ ((p0 ∧ False) → (p5 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case inl assump_15 =>
          apply Or.inr
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
        case inr assump_16 =>
          apply Or.inr
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            apply False.elim assump_30
  case inr assump_4 =>
    cases assump_4
    case intro assump_35 assump_36 =>
      cases assump_35
      case inl assump_37 =>
        cases assump_1
        case inl assump_43 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_37
        case inr assump_44 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          exact assump_37
      case inr assump_38 =>
        apply False.elim assump_38


variable (p4 p6 p1 p7 p5 p3 p2 : Prop)
theorem file99_74832 : (((((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) → False) → ((((p5 → p5) ∧ (p1 ∨ p3)) → ((p1 ∨ True) ∧ (p3 → p6))) → (((p2 → p2) ∨ (p6 ∨ p5)) → ((p5 ∨ p7) → (True → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    cases assump_3
    case inl assump_12 =>
      have assump_88 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
        apply Or.inl
        apply Or.inr
        intro assump_21
        apply True.intro
      let assump_20 := assump_1 assump_88
      apply False.elim assump_20
    case inr assump_13 =>
      cases assump_13
      case inl assump_25 =>
        have assump_89 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
          apply Or.inl
          apply Or.inr
          intro assump_34
          apply True.intro
        let assump_33 := assump_1 assump_89
        apply False.elim assump_33
      case inr assump_26 =>
        have assump_90 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
          apply Or.inl
          apply Or.inr
          intro assump_45
          apply True.intro
        let assump_44 := assump_1 assump_90
        apply False.elim assump_44
  case inr assump_9 =>
    cases assump_3
    case inl assump_51 =>
      have assump_91 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
        apply Or.inl
        apply Or.inr
        intro assump_60
        apply True.intro
      let assump_59 := assump_1 assump_91
      apply False.elim assump_59
    case inr assump_52 =>
      cases assump_52
      case inl assump_64 =>
        have assump_92 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
          apply Or.inl
          apply Or.inr
          intro assump_73
          apply True.intro
        let assump_72 := assump_1 assump_92
        apply False.elim assump_72
      case inr assump_65 =>
        have assump_93 : (((p1 ∧ True) ∨ (p7 → True)) ∨ ((p4 → p6) ∧ (p2 → p7))) := by
          apply Or.inl
          apply Or.inr
          intro assump_84
          apply True.intro
        let assump_83 := assump_1 assump_93
        apply False.elim assump_83


variable (p5 p6 p2 p0 p1 p7 p4 : Prop)
theorem file99_77091 : (((((p0 → p1) → False) ∧ ((False → False) ∧ (p4 ∧ p1))) → (((p5 → False) → (p0 ∧ p6)) → ((False → False) ∨ (False ∧ p2)))) ∨ ((((p6 → p1) ∨ (p4 ∨ p7)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19


variable (p3 p2 p0 p6 p4 p1 : Prop)
theorem file99_77625 : (((((p4 ∧ p3) ∧ (p3 → False)) → ((p6 ∧ True) ∧ (p1 → True))) ∨ (((False → False) → False) → ((p6 → False) → False))) ∨ ((((p2 → False) → (p0 ∨ p3)) → ((p0 ∨ p1) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_17 : p3 := by
        exact assump_5
      let assump_12 := assump_3 assump_17
      apply False.elim assump_12
  apply True.intro
  intro assump_16
  apply True.intro


variable (p3 p0 p6 p2 p4 p7 : Prop)
theorem file99_78247 : (((((p2 → False) ∧ (p6 → p0)) → ((p7 ∧ False) → False)) ∨ (((p0 → False) → (p4 → False)) ∨ ((p0 ∧ p3) ∨ (False → False)))) ∨ ((((p2 ∨ p2) → (True → p0)) ∨ ((True → p2) → (p0 ∧ p4))) ∨ (((True ∧ p3) → (p7 ∧ p0)) ∨ ((p2 → p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p5 p2 p3 p4 p1 p7 : Prop)
theorem file99_78694 : (((((False → p2) → (p2 → p2)) → False) → False) ∨ ((((False ∧ p7) ∧ (False → False)) ∨ ((False → False) ∧ (p2 ∨ p4))) ∨ (((p1 ∨ p2) ∨ (p2 → p5)) ∨ ((p5 ∧ p3) ∨ (True ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  have assump_14 : ((False → p2) → (p2 → p2)) := by
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p3 p5 p7 p2 p0 p1 p6 : Prop)
theorem file99_79148 : (((((p0 → p6) → (p2 ∨ p2)) → ((p3 → False) ∨ (p7 → False))) → (((False ∨ p4) ∧ (p3 → p7)) → ((p7 → True) ∨ (True ∧ p2)))) ∨ ((((True → False) ∧ (True → p1)) ∨ ((p6 ∨ p2) ∨ (p5 ∨ p5))) ∨ (((p1 → p4) ∧ (p0 → False)) ∧ ((p0 ∨ p6) → False)))) := by
  apply Or.inl
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case inl assump_20 =>
      apply False.elim assump_20
    case inr assump_21 =>
      apply Or.inl
      intro assump_30
      apply True.intro


variable (p7 p1 p3 p2 p5 p4 : Prop)
theorem file99_79727 : ((((((p2 → False) ∨ (p2 → False)) ∨ ((p3 ∨ p7) → (p1 ∧ p1))) → (((p4 ∧ True) → (p4 ∨ p5)) ∨ ((p1 ∧ p4) → False))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p2 → False) ∨ (p2 → False)) ∨ ((p3 ∨ p7) → (p1 ∧ p1))) → (((p4 ∧ True) → (p4 ∨ p5)) ∨ ((p1 ∧ p4) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          apply Or.inl
          exact assump_13
      case inr assump_9 =>
        apply Or.inl
        intro assump_21
        cases assump_21
        case intro assump_22 assump_23 =>
          apply Or.inl
          exact assump_22
    case inr assump_7 =>
      apply Or.inl
      intro assump_30
      cases assump_30
      case intro assump_31 assump_32 =>
        apply Or.inl
        exact assump_31
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p6 p4 p5 p7 p3 p1 : Prop)
theorem file99_80775 : ((((((p3 ∧ p1) ∨ (p5 → True)) ∧ ((False → p7) → False)) ∨ (((p5 ∧ p4) ∧ (p3 ∧ p4)) ∧ ((p6 ∧ False) ∧ (False ∨ p3)))) ∧ ((((p7 ∨ True) ∧ (p1 ∧ False)) → False) → False)) → False) := by
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
          case intro assump_10 assump_11 =>
            have assump_100 : (((p7 ∨ True) ∧ (p1 ∧ False)) → False) := by
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_23
                  case intro assump_28 assump_29 =>
                    apply False.elim assump_29
                case inr assump_25 =>
                  cases assump_23
                  case intro assump_36 assump_37 =>
                    apply False.elim assump_37
            let assump_20 := assump_3 assump_100
            apply False.elim assump_20
        case inr assump_9 =>
          have assump_101 : (((p7 ∨ True) ∧ (p1 ∧ False)) → False) := by
            intro assump_52
            cases assump_52
            case intro assump_53 assump_54 =>
              cases assump_53
              case inl assump_55 =>
                cases assump_54
                case intro assump_59 assump_60 =>
                  apply False.elim assump_60
              case inr assump_56 =>
                cases assump_54
                case intro assump_67 assump_68 =>
                  apply False.elim assump_68
          let assump_51 := assump_3 assump_101
          apply False.elim assump_51
    case inr assump_5 =>
      cases assump_5
      case intro assump_76 assump_77 =>
        cases assump_76
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            cases assump_79
            case intro assump_86 assump_87 =>
              cases assump_77
              case intro assump_92 assump_93 =>
                cases assump_92
                case intro assump_94 assump_95 =>
                  apply False.elim assump_95


variable (p2 p5 p1 p6 p0 p7 : Prop)
theorem file99_83101 : (((((p0 ∧ True) → (p6 → p2)) ∨ ((p7 → p5) → False)) → False) → ((((p6 ∧ False) ∧ (p0 → False)) → False) ∨ (((p2 ∨ p1) → (False → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p3 p7 p2 p4 p1 p6 : Prop)
theorem file99_83502 : ((((((p2 ∧ False) → (p7 ∧ p6)) ∧ ((p4 ∨ p3) → (p6 ∧ p3))) ∧ (((p4 ∧ p7) ∨ (False ∨ True)) → ((p2 ∨ p1) → False))) ∧ ((((False → False) → (p4 ∨ True)) ∨ ((False ∧ p1) → (p1 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_23 : (((False → False) → (p4 ∨ True)) ∨ ((False ∧ p1) → (p1 ∨ p6))) := by
          apply Or.inl
          intro assump_17
          apply Or.inr
          apply True.intro
        let assump_16 := assump_3 assump_23
        apply False.elim assump_16


variable (p1 p7 p0 p6 p2 : Prop)
theorem file99_84218 : (((((p1 ∧ False) → (p0 ∨ p1)) → ((p1 ∨ p2) ∧ (False → p6))) ∧ (((False → False) ∧ (True ∨ p7)) → False)) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    have assump_35 : ((False → False) ∧ (True ∨ p7)) := by
      apply And.intro
      intro assump_29
      apply False.elim assump_29
      apply Or.inl
      apply True.intro
    let assump_28 := assump_23 assump_35
    apply False.elim assump_28


variable (p5 p3 p2 p0 p1 p7 p4 : Prop)
theorem file99_84723 : (((((p2 → False) → (p0 ∨ True)) ∨ ((p3 → False) ∨ (p4 ∧ True))) ∧ (((p5 → False) → False) ∨ ((p7 ∨ True) → False))) → ((((True → False) ∧ (p5 → False)) → ((p2 ∨ p3) → (p4 → p2))) ∨ (((p0 ∧ p1) ∧ (p1 ∨ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        intro assump_14
        cases assump_13
        case inl assump_17 =>
          cases assump_12
          case intro assump_21 assump_22 =>
            exact assump_17
        case inr assump_18 =>
          cases assump_12
          case intro assump_29 assump_30 =>
            have assump_204 : True := by
              apply True.intro
            let assump_36 := assump_29 assump_204
            apply False.elim assump_36
      case inr assump_9 =>
        apply Or.inl
        intro assump_42
        intro assump_43
        intro assump_44
        cases assump_43
        case inl assump_47 =>
          cases assump_42
          case intro assump_51 assump_52 =>
            exact assump_47
        case inr assump_48 =>
          cases assump_42
          case intro assump_59 assump_60 =>
            have assump_205 : True := by
              apply True.intro
            let assump_66 := assump_59 assump_205
            apply False.elim assump_66
    case inr assump_5 =>
      cases assump_5
      case inl assump_70 =>
        cases assump_3
        case inl assump_74 =>
          apply Or.inl
          intro assump_78
          intro assump_79
          intro assump_80
          cases assump_79
          case inl assump_83 =>
            cases assump_78
            case intro assump_87 assump_88 =>
              exact assump_83
          case inr assump_84 =>
            cases assump_78
            case intro assump_95 assump_96 =>
              have assump_206 : True := by
                apply True.intro
              let assump_102 := assump_95 assump_206
              apply False.elim assump_102
        case inr assump_75 =>
          apply Or.inl
          intro assump_108
          intro assump_109
          intro assump_110
          cases assump_109
          case inl assump_113 =>
            cases assump_108
            case intro assump_117 assump_118 =>
              exact assump_113
          case inr assump_114 =>
            cases assump_108
            case intro assump_125 assump_126 =>
              have assump_207 : True := by
                apply True.intro
              let assump_132 := assump_125 assump_207
              apply False.elim assump_132
      case inr assump_71 =>
        cases assump_71
        case intro assump_136 assump_137 =>
          cases assump_3
          case inl assump_142 =>
            apply Or.inl
            intro assump_146
            intro assump_147
            intro assump_148
            cases assump_147
            case inl assump_151 =>
              cases assump_146
              case intro assump_155 assump_156 =>
                exact assump_151
            case inr assump_152 =>
              cases assump_146
              case intro assump_163 assump_164 =>
                have assump_208 : True := by
                  apply True.intro
                let assump_170 := assump_163 assump_208
                apply False.elim assump_170
          case inr assump_143 =>
            apply Or.inl
            intro assump_176
            intro assump_177
            intro assump_178
            cases assump_177
            case inl assump_181 =>
              cases assump_176
              case intro assump_185 assump_186 =>
                exact assump_181
            case inr assump_182 =>
              cases assump_176
              case intro assump_193 assump_194 =>
                have assump_209 : True := by
                  apply True.intro
                let assump_200 := assump_193 assump_209
                apply False.elim assump_200


variable (p1 p3 p6 p7 p0 p5 : Prop)
theorem file99_88815 : (((((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) → False) → ((((p0 → p6) ∨ (p0 → False)) ∧ ((p3 ∨ p6) ∨ (p3 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          have assump_193 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
            intro assump_18
            intro assump_19
            intro assump_20
            cases assump_18
            case intro assump_25 assump_26 =>
              cases assump_25
              case intro assump_27 assump_28 =>
                have assump_194 : True := by
                  apply True.intro
                let assump_35 := assump_26 assump_194
                apply False.elim assump_35
          let assump_17 := assump_1 assump_193
          apply False.elim assump_17
        case inr assump_12 =>
          have assump_195 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
            intro assump_47
            intro assump_48
            intro assump_49
            cases assump_47
            case intro assump_54 assump_55 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                have assump_196 : True := by
                  apply True.intro
                let assump_64 := assump_55 assump_196
                apply False.elim assump_64
          let assump_46 := assump_1 assump_195
          apply False.elim assump_46
      case inr assump_10 =>
        have assump_197 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
          intro assump_76
          intro assump_77
          intro assump_78
          cases assump_76
          case intro assump_83 assump_84 =>
            cases assump_83
            case intro assump_85 assump_86 =>
              have assump_198 : True := by
                apply True.intro
              let assump_93 := assump_84 assump_198
              apply False.elim assump_93
        let assump_75 := assump_1 assump_197
        apply False.elim assump_75
    case inr assump_6 =>
      cases assump_4
      case inl assump_102 =>
        cases assump_102
        case inl assump_104 =>
          have assump_199 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
            intro assump_111
            intro assump_112
            intro assump_113
            cases assump_111
            case intro assump_118 assump_119 =>
              cases assump_118
              case intro assump_120 assump_121 =>
                have assump_200 : True := by
                  apply True.intro
                let assump_128 := assump_119 assump_200
                apply False.elim assump_128
          let assump_110 := assump_1 assump_199
          apply False.elim assump_110
        case inr assump_105 =>
          have assump_201 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
            intro assump_140
            intro assump_141
            intro assump_142
            cases assump_140
            case intro assump_147 assump_148 =>
              cases assump_147
              case intro assump_149 assump_150 =>
                have assump_202 : True := by
                  apply True.intro
                let assump_157 := assump_148 assump_202
                apply False.elim assump_157
          let assump_139 := assump_1 assump_201
          apply False.elim assump_139
      case inr assump_103 =>
        have assump_203 : (((p5 ∧ True) ∧ (True → False)) → ((p5 → p3) → (p7 → False))) := by
          intro assump_169
          intro assump_170
          intro assump_171
          cases assump_169
          case intro assump_176 assump_177 =>
            cases assump_176
            case intro assump_178 assump_179 =>
              have assump_204 : True := by
                apply True.intro
              let assump_186 := assump_177 assump_204
              apply False.elim assump_186
        let assump_168 := assump_1 assump_203
        apply False.elim assump_168


variable (p4 p0 p6 p2 p5 : Prop)
theorem file99_93042 : (((((p6 → False) ∧ (True → False)) → False) ∨ (((p5 → False) → False) → ((p4 → p2) ∨ (True ∧ p2)))) ∨ ((((p4 → p0) → False) ∧ ((p5 ∧ p6) ∧ (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : True := by
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p2 p0 p7 p3 p5 : Prop)
theorem file99_93494 : (((((p0 ∧ p3) → (p2 ∨ p7)) → ((p0 → p5) → (p7 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p0 ∧ p3) → (p2 ∨ p7)) → ((p0 → p5) → (p7 ∨ True))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p4 p1 p2 p0 p5 p6 : Prop)
theorem file99_93871 : (((((p2 → False) ∧ (p4 → False)) → ((False ∧ p2) → (p0 → False))) → False) → ((((True → p2) → (p5 → False)) → ((p6 ∨ p1) → False)) ∧ (((p4 ∧ p2) → (True → False)) → False))) := by
  intro assump_8
  apply And.intro
  intro assump_9
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    have assump_69 : (((p2 → False) ∧ (p4 → False)) → ((False ∧ p2) → (p0 → False))) := by
      intro assump_20
      intro assump_21
      intro assump_22
      cases assump_21
      case intro assump_25 assump_26 =>
        apply False.elim assump_25
    let assump_19 := assump_8 assump_69
    apply False.elim assump_19
  case inr assump_12 =>
    have assump_70 : (((p2 → False) ∧ (p4 → False)) → ((False ∧ p2) → (p0 → False))) := by
      intro assump_39
      intro assump_40
      intro assump_41
      cases assump_40
      case intro assump_44 assump_45 =>
        apply False.elim assump_44
    let assump_38 := assump_8 assump_70
    apply False.elim assump_38
  intro assump_51
  have assump_71 : (((p2 → False) ∧ (p4 → False)) → ((False ∧ p2) → (p0 → False))) := by
    intro assump_57
    intro assump_58
    intro assump_59
    cases assump_58
    case intro assump_62 assump_63 =>
      apply False.elim assump_62
  let assump_56 := assump_8 assump_71
  apply False.elim assump_56


variable (p0 p4 p5 p3 p7 p6 p1 : Prop)
theorem file99_95225 : (((((p0 ∧ False) ∧ (p0 ∨ p7)) ∧ ((p0 → False) ∧ (False → False))) → (((p1 → p1) ∧ (p4 ∨ False)) ∧ ((p0 ∨ p6) ∨ (p1 ∨ p1)))) ∨ ((((p0 ∧ p4) → False) → ((p1 → False) → (False ∨ False))) ∧ (((p6 ∧ p0) ∨ (p5 → p5)) → ((p5 → p6) ∧ (p3 ∧ p6))))) := by
  apply Or.inl
  intro assump_88
  apply And.intro
  apply And.intro
  intro assump_89
  cases assump_88
  case intro assump_92 assump_93 =>
    cases assump_92
    case intro assump_94 assump_95 =>
      cases assump_94
      case intro assump_96 assump_97 =>
        apply False.elim assump_97
  cases assump_88
  case intro assump_102 assump_103 =>
    cases assump_102
    case intro assump_104 assump_105 =>
      cases assump_104
      case intro assump_106 assump_107 =>
        apply False.elim assump_107
  cases assump_88
  case intro assump_112 assump_113 =>
    cases assump_112
    case intro assump_114 assump_115 =>
      cases assump_114
      case intro assump_116 assump_117 =>
        apply False.elim assump_117


variable (p7 p5 p4 p1 p2 : Prop)
theorem file99_96260 : ((((((p2 → False) ∧ (p2 ∨ False)) → ((p5 → False) ∨ (p1 ∧ p1))) → (((p4 → False) → (False → False)) ∨ ((False → p7) ∧ (False ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 → False) ∧ (p2 ∨ False)) → ((p5 → False) ∨ (p1 ∧ p1))) → (((p4 → False) → (False → False)) ∨ ((False → p7) ∧ (False ∧ True)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p0 p1 p2 p7 : Prop)
theorem file99_96822 : ((((((p4 → False) ∧ (p2 ∧ p2)) ∧ ((p4 ∧ p0) ∧ (p7 → p1))) → False) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p4 → False) ∧ (p2 ∧ p2)) ∧ ((p4 ∧ p0) ∧ (p7 → p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              have assump_41 : p4 := by
                exact assump_20
              let assump_33 := assump_8 assump_41
              apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p2 p7 p3 : Prop)
theorem file99_97640 : (((((p2 → p3) → False) → ((p2 → True) → (p7 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p2 → p3) → False) → ((p2 → True) → (p7 ∨ True))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p2 p3 p4 p7 p6 p5 : Prop)
theorem file99_98016 : (((((p3 ∧ p5) ∨ (p7 ∧ p2)) ∧ ((False ∧ p5) ∧ (p0 → p2))) → (((p4 ∨ p3) ∨ (p6 ∨ p5)) ∧ ((True ∨ False) ∨ (p4 ∧ True)))) ∨ ((((p0 ∨ p7) ∨ (p5 ∧ False)) → ((True → False) ∨ (p2 ∨ p4))) → (((p5 ∧ p2) ∨ (p7 ∧ p5)) ∨ ((p0 ∧ p7) ∨ (p4 ∨ p2))))) := by
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
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_3
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
  cases assump_1
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_31
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_42
    case inr assump_33 =>
      cases assump_33
      case intro assump_46 assump_47 =>
        cases assump_31
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            apply False.elim assump_54


variable (p3 p0 p2 : Prop)
theorem file99_99548 : (((((p2 ∧ False) → False) → False) → False) ∨ ((((False → p3) → (False ∧ p0)) → ((True → False) → False)) → (((p2 → False) → False) → False))) := by
  apply Or.inl
  intro assump_23
  have assump_37 : ((p2 ∧ False) → False) := by
    intro assump_27
    cases assump_27
    case intro assump_28 assump_29 =>
      apply False.elim assump_29
  let assump_26 := assump_23 assump_37
  apply False.elim assump_26


variable (p6 p3 p5 p7 p1 p0 p2 p4 : Prop)
theorem file99_100023 : (((((p5 ∨ p2) ∧ (p2 → False)) ∧ ((p3 → False) → (p4 ∨ True))) → False) → ((((p2 → p3) → (p4 ∨ True)) → ((p5 ∨ p4) → (False → p2))) ∨ (((p6 → p0) ∨ (p7 ∧ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p3 p1 p6 p0 p2 p5 : Prop)
theorem file99_100369 : (((((p1 → p1) → False) → False) → False) → ((((p5 → False) → (p6 ∨ True)) ∧ ((p0 → False) ∨ (p2 → False))) ∧ (((p5 ∨ p0) → (p3 ∨ p2)) → ((False → p1) → (p1 → p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  apply Or.inr
  apply True.intro
  apply Or.inl
  intro assump_9
  have assump_52 : (((p1 → p1) → False) → False) := by
    intro assump_14
    have assump_53 : (p1 → p1) := by
      intro assump_18
      exact assump_18
    let assump_17 := assump_14 assump_53
    apply False.elim assump_17
  let assump_13 := assump_1 assump_52
  apply False.elim assump_13
  intro assump_27
  intro assump_28
  intro assump_29
  have assump_54 : (((p1 → p1) → False) → False) := by
    intro assump_39
    have assump_55 : (p1 → p1) := by
      intro assump_43
      exact assump_43
    let assump_42 := assump_39 assump_55
    apply False.elim assump_42
  let assump_38 := assump_1 assump_54
  apply False.elim assump_38


variable (p1 p2 p3 p6 p5 : Prop)
theorem file99_101378 : ((((((p5 ∧ p1) ∧ (False ∨ False)) → False) ∨ (((p3 → False) ∨ (False ∨ False)) ∧ ((p2 → False) ∧ (p6 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p5 ∧ p1) ∧ (False ∨ False)) → False) ∨ (((p3 → False) ∨ (False ∨ False)) ∧ ((p2 → False) ∧ (p6 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p3 p6 p2 p7 : Prop)
theorem file99_102098 : ((((((True → False) → False) ∨ ((p1 ∧ p5) ∨ (p3 ∧ p2))) ∨ (((p3 → p2) → (p7 → False)) ∧ ((p1 ∨ p6) → (p1 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p1 ∧ p5) ∨ (p3 ∧ p2))) ∨ (((p3 → p2) → (p7 → False)) ∧ ((p1 ∨ p6) → (p1 ∧ p2)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p3 p0 p7 p6 p2 p4 : Prop)
theorem file99_102695 : (((((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) → False) → ((((True ∨ p7) → (p6 ∨ p6)) ∨ ((p7 ∨ p7) → False)) ∧ (((p4 ∨ p5) → False) ∧ ((p7 → False) → (True → False))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_296 : (((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) := by
      intro assump_10
      apply And.intro
      cases assump_10
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
      apply And.intro
      cases assump_10
      case intro assump_27 assump_28 =>
        cases assump_27
        case inl assump_29 =>
          cases assump_28
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
        case inr assump_30 =>
          cases assump_28
          case intro assump_39 assump_40 =>
            apply False.elim assump_39
      cases assump_10
      case intro assump_43 assump_44 =>
        cases assump_43
        case inl assump_45 =>
          cases assump_44
          case intro assump_49 assump_50 =>
            apply False.elim assump_49
        case inr assump_46 =>
          cases assump_44
          case intro assump_55 assump_56 =>
            apply False.elim assump_55
    let assump_9 := assump_1 assump_296
    apply False.elim assump_9
  case inr assump_6 =>
    have assump_297 : (((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) := by
      intro assump_66
      apply And.intro
      cases assump_66
      case intro assump_67 assump_68 =>
        cases assump_67
        case inl assump_69 =>
          cases assump_68
          case intro assump_73 assump_74 =>
            apply False.elim assump_73
        case inr assump_70 =>
          cases assump_68
          case intro assump_79 assump_80 =>
            apply False.elim assump_79
      apply And.intro
      cases assump_66
      case intro assump_83 assump_84 =>
        cases assump_83
        case inl assump_85 =>
          cases assump_84
          case intro assump_89 assump_90 =>
            apply False.elim assump_89
        case inr assump_86 =>
          cases assump_84
          case intro assump_95 assump_96 =>
            apply False.elim assump_95
      cases assump_66
      case intro assump_99 assump_100 =>
        cases assump_99
        case inl assump_101 =>
          cases assump_100
          case intro assump_105 assump_106 =>
            apply False.elim assump_105
        case inr assump_102 =>
          cases assump_100
          case intro assump_111 assump_112 =>
            apply False.elim assump_111
    let assump_65 := assump_1 assump_297
    apply False.elim assump_65
  apply And.intro
  intro assump_118
  cases assump_118
  case inl assump_119 =>
    have assump_298 : (((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) := by
      intro assump_126
      apply And.intro
      cases assump_126
      case intro assump_127 assump_128 =>
        cases assump_127
        case inl assump_129 =>
          cases assump_128
          case intro assump_133 assump_134 =>
            apply False.elim assump_133
        case inr assump_130 =>
          cases assump_128
          case intro assump_139 assump_140 =>
            apply False.elim assump_139
      apply And.intro
      cases assump_126
      case intro assump_143 assump_144 =>
        cases assump_143
        case inl assump_145 =>
          cases assump_144
          case intro assump_149 assump_150 =>
            apply False.elim assump_149
        case inr assump_146 =>
          cases assump_144
          case intro assump_155 assump_156 =>
            apply False.elim assump_155
      cases assump_126
      case intro assump_159 assump_160 =>
        cases assump_159
        case inl assump_161 =>
          cases assump_160
          case intro assump_165 assump_166 =>
            apply False.elim assump_165
        case inr assump_162 =>
          cases assump_160
          case intro assump_171 assump_172 =>
            apply False.elim assump_171
    let assump_125 := assump_1 assump_298
    apply False.elim assump_125
  case inr assump_120 =>
    have assump_299 : (((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) := by
      intro assump_183
      apply And.intro
      cases assump_183
      case intro assump_184 assump_185 =>
        cases assump_184
        case inl assump_186 =>
          cases assump_185
          case intro assump_190 assump_191 =>
            apply False.elim assump_190
        case inr assump_187 =>
          cases assump_185
          case intro assump_196 assump_197 =>
            apply False.elim assump_196
      apply And.intro
      cases assump_183
      case intro assump_200 assump_201 =>
        cases assump_200
        case inl assump_202 =>
          cases assump_201
          case intro assump_206 assump_207 =>
            apply False.elim assump_206
        case inr assump_203 =>
          cases assump_201
          case intro assump_212 assump_213 =>
            apply False.elim assump_212
      cases assump_183
      case intro assump_216 assump_217 =>
        cases assump_216
        case inl assump_218 =>
          cases assump_217
          case intro assump_222 assump_223 =>
            apply False.elim assump_222
        case inr assump_219 =>
          cases assump_217
          case intro assump_228 assump_229 =>
            apply False.elim assump_228
    let assump_182 := assump_1 assump_299
    apply False.elim assump_182
  intro assump_235
  intro assump_236
  have assump_300 : (((p0 ∨ p3) ∧ (False ∧ p5)) → ((p3 ∨ p0) ∧ (p4 ∧ p2))) := by
    intro assump_244
    apply And.intro
    cases assump_244
    case intro assump_245 assump_246 =>
      cases assump_245
      case inl assump_247 =>
        cases assump_246
        case intro assump_251 assump_252 =>
          apply False.elim assump_251
      case inr assump_248 =>
        cases assump_246
        case intro assump_257 assump_258 =>
          apply False.elim assump_257
    apply And.intro
    cases assump_244
    case intro assump_261 assump_262 =>
      cases assump_261
      case inl assump_263 =>
        cases assump_262
        case intro assump_267 assump_268 =>
          apply False.elim assump_267
      case inr assump_264 =>
        cases assump_262
        case intro assump_273 assump_274 =>
          apply False.elim assump_273
    cases assump_244
    case intro assump_277 assump_278 =>
      cases assump_277
      case inl assump_279 =>
        cases assump_278
        case intro assump_283 assump_284 =>
          apply False.elim assump_283
      case inr assump_280 =>
        cases assump_278
        case intro assump_289 assump_290 =>
          apply False.elim assump_289
  let assump_243 := assump_1 assump_300
  apply False.elim assump_243


variable (p6 p5 p2 p1 p3 p7 : Prop)
theorem file99_109845 : ((((((p6 ∨ p3) → False) → ((p6 → False) ∨ (p2 → False))) ∨ (((p7 ∨ p2) → False) ∧ ((p5 ∨ p1) ∧ (p5 ∨ p1)))) → False) → False) := by
  intro assump_7
  have assump_25 : ((((p6 ∨ p3) → False) → ((p6 → False) ∨ (p2 → False))) ∨ (((p7 ∨ p2) → False) ∧ ((p5 ∨ p1) ∧ (p5 ∨ p1)))) := by
    apply Or.inl
    intro assump_11
    apply Or.inl
    intro assump_14
    have assump_26 : (p6 ∨ p3) := by
      apply Or.inl
      exact assump_14
    let assump_18 := assump_11 assump_26
    apply False.elim assump_18
  let assump_10 := assump_7 assump_25
  apply False.elim assump_10


variable (p0 p2 p7 p6 p1 p5 p4 : Prop)
theorem file99_110479 : (((((False ∨ p4) ∧ (p2 → p7)) → ((False → False) ∨ (p6 ∧ p2))) → False) → ((((True → p7) → (p0 → False)) → ((False → p6) → False)) ∧ (((p5 ∨ p6) → (False → False)) ∧ ((p4 ∧ p1) → (p0 → p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_62 : (((False ∨ p4) ∧ (p2 → p7)) → ((False → False) ∨ (p6 ∧ p2))) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        apply False.elim assump_14
      case inr assump_15 =>
        apply Or.inl
        intro assump_22
        apply False.elim assump_22
  let assump_10 := assump_1 assump_62
  apply False.elim assump_10
  apply And.intro
  intro assump_28
  intro assump_29
  apply False.elim assump_29
  intro assump_32
  intro assump_33
  cases assump_32
  case intro assump_36 assump_37 =>
    have assump_63 : (((False ∨ p4) ∧ (p2 → p7)) → ((False → False) ∨ (p6 ∧ p2))) := by
      intro assump_45
      cases assump_45
      case intro assump_46 assump_47 =>
        cases assump_46
        case inl assump_48 =>
          apply False.elim assump_48
        case inr assump_49 =>
          apply Or.inl
          intro assump_56
          apply False.elim assump_56
    let assump_44 := assump_1 assump_63
    apply False.elim assump_44


variable (p7 p0 p3 p5 p4 p6 p2 : Prop)
theorem file99_111857 : (((((p7 → False) → False) → False) ∨ (((p0 → False) → False) → False)) → ((((p7 → False) ∧ (p7 ∧ p4)) ∨ ((p7 ∨ p4) ∨ (True → p5))) → (((True ∨ p4) ∨ (p2 ∨ False)) ∨ ((p6 → False) → (p3 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case inl assump_15 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_16 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
  case inr assump_4 =>
    cases assump_4
    case inl assump_21 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_1
        case inl assump_27 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_28 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_24 =>
        cases assump_1
        case inl assump_35 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_36 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply True.intro
    case inr assump_22 =>
      cases assump_1
      case inl assump_43 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_44 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p2 p1 p3 p5 p7 p0 p6 : Prop)
theorem file99_113560 : ((((((p1 → True) ∧ (p6 ∨ p3)) ∧ ((p6 → False) ∨ (p3 ∧ p3))) → False) ∧ ((((True → False) → False) ∨ ((p7 ∧ p2) → False)) ∧ (((p7 ∧ p5) → (p0 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_30 : ((p7 ∧ p5) → (p0 → True)) := by
          intro assump_15
          intro assump_16
          apply True.intro
        let assump_14 := assump_7 assump_30
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_31 : ((p7 ∧ p5) → (p0 → True)) := by
          intro assump_25
          intro assump_26
          apply True.intro
        let assump_24 := assump_7 assump_31
        apply False.elim assump_24


variable (p7 p5 p4 p3 p6 p2 p0 p1 : Prop)
theorem file99_114430 : (((((p1 ∨ p0) ∧ (p1 ∧ p7)) → ((p1 → False) → False)) ∨ (((p5 → True) ∨ (False ∨ p7)) → False)) ∨ ((((p2 ∨ True) → (p6 ∨ p6)) ∧ ((p2 ∧ p4) → False)) ∨ (((p1 → p1) ∨ (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        have assump_39 : p1 := by
          exact assump_11
        let assump_20 := assump_2 assump_39
        apply False.elim assump_20
    case inr assump_8 =>
      cases assump_6
      case intro assump_26 assump_27 =>
        have assump_40 : p1 := by
          exact assump_26
        let assump_35 := assump_2 assump_40
        apply False.elim assump_35


variable (p3 p2 p5 p4 p6 : Prop)
theorem file99_115266 : (((((p5 → False) ∧ (p5 ∧ p2)) ∧ ((p5 ∧ p5) ∨ (p3 → False))) → False) ∧ ((((False → p6) → False) → False) → (((p4 → True) → (p5 ∧ p6)) → ((False ∧ p5) → (p5 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            have assump_49 : p5 := by
              exact assump_17
            let assump_26 := assump_4 assump_49
            apply False.elim assump_26
        case inr assump_15 =>
          have assump_50 : p5 := by
            exact assump_8
          let assump_35 := assump_4 assump_50
          apply False.elim assump_35
  intro assump_39
  intro assump_40
  intro assump_41
  intro assump_42
  cases assump_41
  case intro assump_45 assump_46 =>
    apply False.elim assump_45


variable (p4 p5 p2 p6 p1 p3 p7 : Prop)
theorem file99_116315 : (((((p4 ∨ True) ∧ (p3 ∧ p3)) → ((p7 ∧ p5) ∧ (False ∨ p7))) → (((p4 → True) → False) → ((p2 ∨ p1) → (p7 → False)))) ∨ ((((p2 ∨ p7) → (p3 ∨ p6)) ∨ ((p2 ∧ p7) → False)) → (((p1 ∨ p3) ∧ (False → False)) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    have assump_33 : (p4 → True) := by
      intro assump_17
      apply True.intro
    let assump_16 := assump_2 assump_33
    apply False.elim assump_16
  case inr assump_8 =>
    have assump_34 : (p4 → True) := by
      intro assump_29
      apply True.intro
    let assump_28 := assump_2 assump_34
    apply False.elim assump_28


variable (p1 p3 p5 p6 p2 p0 : Prop)
theorem file99_117064 : ((((((p2 → False) ∧ (p3 ∧ p6)) ∨ ((p1 ∨ p5) → False)) → (((p1 ∨ p1) ∧ (False → False)) ∨ ((p6 ∧ p0) → (p2 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p2 → False) ∧ (p3 ∧ p6)) ∨ ((p1 ∨ p5) → False)) → (((p1 ∨ p1) ∧ (False → False)) ∨ ((p6 ∧ p0) → (p2 ∨ p6)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inr
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply Or.inr
            exact assump_19
    case inr assump_7 =>
      apply Or.inr
      intro assump_27
      cases assump_27
      case intro assump_28 assump_29 =>
        apply Or.inr
        exact assump_28
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 p5 p4 p0 p3 p7 p6 : Prop)
theorem file99_118018 : (((((False ∧ p5) ∧ (True ∧ p6)) → ((p3 ∨ p1) ∧ (p6 ∨ p4))) ∨ (((p5 ∧ False) ∧ (p6 → True)) ∨ ((True → p0) → (p7 ∨ False)))) ∨ ((((False → False) ∨ (p3 → p5)) → False) ∧ (((p1 → p0) → (p6 ∧ True)) ∨ ((True ∨ p3) → (p6 → p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      apply False.elim assump_10


variable (p2 p5 p4 p0 p7 p3 : Prop)
theorem file99_118655 : (((((True → p4) ∧ (p2 ∧ p2)) ∧ ((True ∨ p7) → False)) → (((False ∧ p2) → False) → False)) ∨ ((((p5 → False) ∨ (p4 ∨ p3)) ∧ ((p0 ∧ p2) → (p2 ∧ False))) ∧ (((p0 → False) ∨ (p3 ∧ True)) ∧ ((p4 ∨ p4) ∧ (p4 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_23 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_19 := assump_6 assump_23
        apply False.elim assump_19


variable (p6 p7 p1 p0 : Prop)
theorem file99_119315 : (((((False → False) ∧ (False → False)) → False) ∧ (((p6 → p0) ∨ (False → False)) ∨ ((p0 → p7) ∧ (p1 → p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_54 : ((False → False) ∧ (False → False)) := by
          apply And.intro
          intro assump_14
          apply False.elim assump_14
          intro assump_17
          apply False.elim assump_17
        let assump_13 := assump_2 assump_54
        apply False.elim assump_13
      case inr assump_9 =>
        have assump_55 : ((False → False) ∧ (False → False)) := by
          apply And.intro
          intro assump_27
          apply False.elim assump_27
          intro assump_30
          apply False.elim assump_30
        let assump_26 := assump_2 assump_55
        apply False.elim assump_26
    case inr assump_7 =>
      cases assump_7
      case intro assump_36 assump_37 =>
        have assump_56 : ((False → False) ∧ (False → False)) := by
          apply And.intro
          intro assump_45
          apply False.elim assump_45
          intro assump_48
          apply False.elim assump_48
        let assump_44 := assump_2 assump_56
        apply False.elim assump_44


variable (p2 p6 p4 p1 p5 p0 p7 p3 : Prop)
theorem file99_120672 : ((((((p7 → False) ∧ (False ∨ p4)) → ((p0 → False) ∧ (False ∨ p3))) ∧ (((p7 ∧ False) → False) → False)) ∧ ((((p6 ∨ p3) ∧ (False ∨ p1)) ∧ ((p2 ∧ p4) → (False → p4))) → (((p5 ∧ p3) ∨ (p1 ∧ p0)) ∨ ((p6 → p4) ∧ (p4 ∨ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_24 : ((p7 ∧ False) → False) := by
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
      let assump_13 := assump_5 assump_24
      apply False.elim assump_13


variable (p6 p5 p2 p4 p0 p1 : Prop)
theorem file99_121344 : ((((((p6 ∨ p0) ∨ (p0 ∨ True)) ∨ ((False ∨ False) → (p4 ∨ p2))) ∨ (((p0 ∧ True) → False) → ((p5 → p6) ∨ (p2 → False)))) → ((((p2 → True) ∧ (False ∧ p1)) → ((p5 ∨ p4) ∨ (p2 ∧ p2))) → False)) → False) := by
  intro assump_1
  have assump_18 : ((((p6 ∨ p0) ∨ (p0 ∨ True)) ∨ ((False ∨ False) → (p4 ∨ p2))) ∨ (((p0 ∧ True) → False) → ((p5 → p6) ∨ (p2 → False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_18
  have assump_19 : (((p2 → True) ∧ (False ∧ p1)) → ((p5 ∨ p4) ∨ (p2 ∧ p2))) := by
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_5 := assump_4 assump_19
  apply False.elim assump_5


variable (p3 p1 p0 p7 p6 p2 p4 p5 : Prop)
theorem file99_122216 : (((((p4 → False) → (p3 → p5)) ∨ ((p3 ∧ False) ∨ (True ∨ p6))) ∧ (((p1 → False) → False) ∧ ((p5 → False) → (p7 ∨ p4)))) → ((((p4 ∨ p0) ∨ (p3 ∨ p6)) ∧ ((p6 ∧ p4) ∧ (p7 ∨ p1))) → (((p3 ∨ p2) → (p3 → p4)) ∨ ((p4 → p0) → (p3 ∧ True))))) := by
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_14
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            cases assump_22
            case inl assump_29 =>
              cases assump_11
              case intro assump_33 assump_34 =>
                cases assump_33
                case inl assump_35 =>
                  cases assump_34
                  case intro assump_39 assump_40 =>
                    apply Or.inl
                    intro assump_45
                    intro assump_46
                    cases assump_45
                    case inl assump_49 =>
                      exact assump_24
                    case inr assump_50 =>
                      exact assump_24
                case inr assump_36 =>
                  cases assump_36
                  case inl assump_55 =>
                    cases assump_55
                    case intro assump_57 assump_58 =>
                      apply False.elim assump_58
                  case inr assump_56 =>
                    cases assump_56
                    case inl assump_63 =>
                      cases assump_34
                      case intro assump_67 assump_68 =>
                        apply Or.inl
                        intro assump_73
                        intro assump_74
                        cases assump_73
                        case inl assump_77 =>
                          exact assump_24
                        case inr assump_78 =>
                          exact assump_24
                    case inr assump_64 =>
                      cases assump_34
                      case intro assump_85 assump_86 =>
                        apply Or.inl
                        intro assump_91
                        intro assump_92
                        cases assump_91
                        case inl assump_95 =>
                          exact assump_24
                        case inr assump_96 =>
                          exact assump_24
            case inr assump_30 =>
              cases assump_11
              case intro assump_103 assump_104 =>
                cases assump_103
                case inl assump_105 =>
                  cases assump_104
                  case intro assump_109 assump_110 =>
                    apply Or.inl
                    intro assump_115
                    intro assump_116
                    cases assump_115
                    case inl assump_119 =>
                      exact assump_24
                    case inr assump_120 =>
                      exact assump_24
                case inr assump_106 =>
                  cases assump_106
                  case inl assump_125 =>
                    cases assump_125
                    case intro assump_127 assump_128 =>
                      apply False.elim assump_128
                  case inr assump_126 =>
                    cases assump_126
                    case inl assump_133 =>
                      cases assump_104
                      case intro assump_137 assump_138 =>
                        apply Or.inl
                        intro assump_143
                        intro assump_144
                        cases assump_143
                        case inl assump_147 =>
                          exact assump_24
                        case inr assump_148 =>
                          exact assump_24
                    case inr assump_134 =>
                      cases assump_104
                      case intro assump_155 assump_156 =>
                        apply Or.inl
                        intro assump_161
                        intro assump_162
                        cases assump_161
                        case inl assump_165 =>
                          exact assump_24
                        case inr assump_166 =>
                          exact assump_24
      case inr assump_18 =>
        cases assump_14
        case intro assump_173 assump_174 =>
          cases assump_173
          case intro assump_175 assump_176 =>
            cases assump_174
            case inl assump_181 =>
              cases assump_11
              case intro assump_185 assump_186 =>
                cases assump_185
                case inl assump_187 =>
                  cases assump_186
                  case intro assump_191 assump_192 =>
                    apply Or.inl
                    intro assump_197
                    intro assump_198
                    cases assump_197
                    case inl assump_201 =>
                      exact assump_176
                    case inr assump_202 =>
                      exact assump_176
                case inr assump_188 =>
                  cases assump_188
                  case inl assump_207 =>
                    cases assump_207
                    case intro assump_209 assump_210 =>
                      apply False.elim assump_210
                  case inr assump_208 =>
                    cases assump_208
                    case inl assump_215 =>
                      cases assump_186
                      case intro assump_219 assump_220 =>
                        apply Or.inl
                        intro assump_225
                        intro assump_226
                        cases assump_225
                        case inl assump_229 =>
                          exact assump_176
                        case inr assump_230 =>
                          exact assump_176
                    case inr assump_216 =>
                      cases assump_186
                      case intro assump_237 assump_238 =>
                        apply Or.inl
                        intro assump_243
                        intro assump_244
                        cases assump_243
                        case inl assump_247 =>
                          exact assump_176
                        case inr assump_248 =>
                          exact assump_176
            case inr assump_182 =>
              cases assump_11
              case intro assump_255 assump_256 =>
                cases assump_255
                case inl assump_257 =>
                  cases assump_256
                  case intro assump_261 assump_262 =>
                    apply Or.inl
                    intro assump_267
                    intro assump_268
                    cases assump_267
                    case inl assump_271 =>
                      exact assump_176
                    case inr assump_272 =>
                      exact assump_176
                case inr assump_258 =>
                  cases assump_258
                  case inl assump_277 =>
                    cases assump_277
                    case intro assump_279 assump_280 =>
                      apply False.elim assump_280
                  case inr assump_278 =>
                    cases assump_278
                    case inl assump_285 =>
                      cases assump_256
                      case intro assump_289 assump_290 =>
                        apply Or.inl
                        intro assump_295
                        intro assump_296
                        cases assump_295
                        case inl assump_299 =>
                          exact assump_176
                        case inr assump_300 =>
                          exact assump_176
                    case inr assump_286 =>
                      cases assump_256
                      case intro assump_307 assump_308 =>
                        apply Or.inl
                        intro assump_313
                        intro assump_314
                        cases assump_313
                        case inl assump_317 =>
                          exact assump_176
                        case inr assump_318 =>
                          exact assump_176
    case inr assump_16 =>
      cases assump_16
      case inl assump_323 =>
        cases assump_14
        case intro assump_327 assump_328 =>
          cases assump_327
          case intro assump_329 assump_330 =>
            cases assump_328
            case inl assump_335 =>
              cases assump_11
              case intro assump_339 assump_340 =>
                cases assump_339
                case inl assump_341 =>
                  cases assump_340
                  case intro assump_345 assump_346 =>
                    apply Or.inl
                    intro assump_351
                    intro assump_352
                    cases assump_351
                    case inl assump_355 =>
                      exact assump_330
                    case inr assump_356 =>
                      exact assump_330
                case inr assump_342 =>
                  cases assump_342
                  case inl assump_361 =>
                    cases assump_361
                    case intro assump_363 assump_364 =>
                      apply False.elim assump_364
                  case inr assump_362 =>
                    cases assump_362
                    case inl assump_369 =>
                      cases assump_340
                      case intro assump_373 assump_374 =>
                        apply Or.inl
                        intro assump_379
                        intro assump_380
                        cases assump_379
                        case inl assump_383 =>
                          exact assump_330
                        case inr assump_384 =>
                          exact assump_330
                    case inr assump_370 =>
                      cases assump_340
                      case intro assump_391 assump_392 =>
                        apply Or.inl
                        intro assump_397
                        intro assump_398
                        cases assump_397
                        case inl assump_401 =>
                          exact assump_330
                        case inr assump_402 =>
                          exact assump_330
            case inr assump_336 =>
              cases assump_11
              case intro assump_409 assump_410 =>
                cases assump_409
                case inl assump_411 =>
                  cases assump_410
                  case intro assump_415 assump_416 =>
                    apply Or.inl
                    intro assump_421
                    intro assump_422
                    cases assump_421
                    case inl assump_425 =>
                      exact assump_330
                    case inr assump_426 =>
                      exact assump_330
                case inr assump_412 =>
                  cases assump_412
                  case inl assump_431 =>
                    cases assump_431
                    case intro assump_433 assump_434 =>
                      apply False.elim assump_434
                  case inr assump_432 =>
                    cases assump_432
                    case inl assump_439 =>
                      cases assump_410
                      case intro assump_443 assump_444 =>
                        apply Or.inl
                        intro assump_449
                        intro assump_450
                        cases assump_449
                        case inl assump_453 =>
                          exact assump_330
                        case inr assump_454 =>
                          exact assump_330
                    case inr assump_440 =>
                      cases assump_410
                      case intro assump_461 assump_462 =>
                        apply Or.inl
                        intro assump_467
                        intro assump_468
                        cases assump_467
                        case inl assump_471 =>
                          exact assump_330
                        case inr assump_472 =>
                          exact assump_330
      case inr assump_324 =>
        cases assump_14
        case intro assump_479 assump_480 =>
          cases assump_479
          case intro assump_481 assump_482 =>
            cases assump_480
            case inl assump_487 =>
              cases assump_11
              case intro assump_491 assump_492 =>
                cases assump_491
                case inl assump_493 =>
                  cases assump_492
                  case intro assump_497 assump_498 =>
                    apply Or.inl
                    intro assump_503
                    intro assump_504
                    cases assump_503
                    case inl assump_507 =>
                      exact assump_482
                    case inr assump_508 =>
                      exact assump_482
                case inr assump_494 =>
                  cases assump_494
                  case inl assump_513 =>
                    cases assump_513
                    case intro assump_515 assump_516 =>
                      apply False.elim assump_516
                  case inr assump_514 =>
                    cases assump_514
                    case inl assump_521 =>
                      cases assump_492
                      case intro assump_525 assump_526 =>
                        apply Or.inl
                        intro assump_531
                        intro assump_532
                        cases assump_531
                        case inl assump_535 =>
                          exact assump_482
                        case inr assump_536 =>
                          exact assump_482
                    case inr assump_522 =>
                      cases assump_492
                      case intro assump_543 assump_544 =>
                        apply Or.inl
                        intro assump_549
                        intro assump_550
                        cases assump_549
                        case inl assump_553 =>
                          exact assump_482
                        case inr assump_554 =>
                          exact assump_482
            case inr assump_488 =>
              cases assump_11
              case intro assump_561 assump_562 =>
                cases assump_561
                case inl assump_563 =>
                  cases assump_562
                  case intro assump_567 assump_568 =>
                    apply Or.inl
                    intro assump_573
                    intro assump_574
                    cases assump_573
                    case inl assump_577 =>
                      exact assump_482
                    case inr assump_578 =>
                      exact assump_482
                case inr assump_564 =>
                  cases assump_564
                  case inl assump_583 =>
                    cases assump_583
                    case intro assump_585 assump_586 =>
                      apply False.elim assump_586
                  case inr assump_584 =>
                    cases assump_584
                    case inl assump_591 =>
                      cases assump_562
                      case intro assump_595 assump_596 =>
                        apply Or.inl
                        intro assump_601
                        intro assump_602
                        cases assump_601
                        case inl assump_605 =>
                          exact assump_482
                        case inr assump_606 =>
                          exact assump_482
                    case inr assump_592 =>
                      cases assump_562
                      case intro assump_613 assump_614 =>
                        apply Or.inl
                        intro assump_619
                        intro assump_620
                        cases assump_619
                        case inl assump_623 =>
                          exact assump_482
                        case inr assump_624 =>
                          exact assump_482


variable (p4 p0 p5 p6 p2 p3 : Prop)
theorem file99_138495 : (((((p0 → False) → False) → ((False → p2) ∨ (False → False))) → False) → ((((p2 → False) ∨ (p3 → p5)) ∧ ((p2 ∨ False) → False)) ∧ (((p4 → p4) ∨ (p4 ∨ p3)) → ((True ∨ p6) ∧ (p2 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_136 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
    intro assump_9
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_1 assump_136
  apply False.elim assump_8
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    have assump_137 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
      intro assump_26
      apply Or.inl
      intro assump_29
      apply False.elim assump_29
    let assump_25 := assump_1 assump_137
    apply False.elim assump_25
  case inr assump_20 =>
    apply False.elim assump_20
  intro assump_37
  apply And.intro
  cases assump_37
  case inl assump_38 =>
    apply Or.inl
    apply True.intro
  case inr assump_39 =>
    cases assump_39
    case inl assump_44 =>
      apply Or.inl
      apply True.intro
    case inr assump_45 =>
      apply Or.inl
      apply True.intro
  apply And.intro
  cases assump_37
  case inl assump_54 =>
    have assump_138 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
      intro assump_61
      apply Or.inl
      intro assump_64
      apply False.elim assump_64
    let assump_60 := assump_1 assump_138
    apply False.elim assump_60
  case inr assump_55 =>
    cases assump_55
    case inl assump_70 =>
      have assump_139 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
        intro assump_77
        apply Or.inl
        intro assump_80
        apply False.elim assump_80
      let assump_76 := assump_1 assump_139
      apply False.elim assump_76
    case inr assump_71 =>
      have assump_140 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
        intro assump_91
        apply Or.inl
        intro assump_94
        apply False.elim assump_94
      let assump_90 := assump_1 assump_140
      apply False.elim assump_90
  cases assump_37
  case inl assump_100 =>
    have assump_141 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
      intro assump_107
      apply Or.inl
      intro assump_110
      apply False.elim assump_110
    let assump_106 := assump_1 assump_141
    apply False.elim assump_106
  case inr assump_101 =>
    cases assump_101
    case inl assump_116 =>
      exact assump_116
    case inr assump_117 =>
      have assump_142 : (((p0 → False) → False) → ((False → p2) ∨ (False → False))) := by
        intro assump_127
        apply Or.inl
        intro assump_130
        apply False.elim assump_130
      let assump_126 := assump_1 assump_142
      apply False.elim assump_126


