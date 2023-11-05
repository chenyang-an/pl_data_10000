variable (p3 p4 p2 p5 p7 p6 p0 : Prop)
theorem file42_47 : ((((((p5 ∧ p3) ∧ (p2 ∨ p4)) ∧ ((False ∨ p3) ∧ (p2 → False))) ∧ (((p7 → False) ∧ (p3 ∧ False)) ∨ ((p3 → p6) → (p6 → False)))) ∧ ((((p0 ∧ True) ∨ (p6 → False)) → ((p3 → False) → False)) → False)) → False) := by
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
              cases assump_7
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  apply False.elim assump_22
                case inr assump_23 =>
                  cases assump_5
                  case inl assump_30 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_33
                      case intro assump_36 assump_37 =>
                        apply False.elim assump_37
                  case inr assump_31 =>
                    have assump_130 : (((p0 ∧ True) ∨ (p6 → False)) → ((p3 → False) → False)) := by
                      intro assump_47
                      intro assump_48
                      cases assump_47
                      case inl assump_51 =>
                        cases assump_51
                        case intro assump_53 assump_54 =>
                          have assump_131 : p3 := by
                            exact assump_23
                          let assump_60 := assump_48 assump_131
                          apply False.elim assump_60
                      case inr assump_52 =>
                        have assump_132 : p3 := by
                          exact assump_23
                        let assump_67 := assump_48 assump_132
                        apply False.elim assump_67
                    let assump_46 := assump_3 assump_130
                    apply False.elim assump_46
            case inr assump_17 =>
              cases assump_7
              case intro assump_76 assump_77 =>
                cases assump_76
                case inl assump_78 =>
                  apply False.elim assump_78
                case inr assump_79 =>
                  cases assump_5
                  case inl assump_86 =>
                    cases assump_86
                    case intro assump_88 assump_89 =>
                      cases assump_89
                      case intro assump_92 assump_93 =>
                        apply False.elim assump_93
                  case inr assump_87 =>
                    have assump_133 : (((p0 ∧ True) ∨ (p6 → False)) → ((p3 → False) → False)) := by
                      intro assump_103
                      intro assump_104
                      cases assump_103
                      case inl assump_107 =>
                        cases assump_107
                        case intro assump_109 assump_110 =>
                          have assump_134 : p3 := by
                            exact assump_79
                          let assump_116 := assump_104 assump_134
                          apply False.elim assump_116
                      case inr assump_108 =>
                        have assump_135 : p3 := by
                          exact assump_79
                        let assump_123 := assump_104 assump_135
                        apply False.elim assump_123
                    let assump_102 := assump_3 assump_133
                    apply False.elim assump_102


variable (p3 p4 p5 p7 : Prop)
theorem file42_3739 : (((((p3 ∨ p5) → (p7 ∨ p3)) → False) ∧ (((False → False) → False) ∧ ((False ∨ p4) ∧ (True → p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          have assump_30 : (False → False) := by
            intro assump_24
            apply False.elim assump_24
          let assump_23 := assump_6 assump_30
          apply False.elim assump_23


variable (p1 p4 : Prop)
theorem file42_4404 : ((((((False → False) ∨ (p4 → p1)) → False) → False) → False) → False) := by
  intro assump_5
  have assump_22 : ((((False → False) ∨ (p4 → p1)) → False) → False) := by
    intro assump_9
    have assump_23 : ((False → False) ∨ (p4 → p1)) := by
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_9 assump_23
    apply False.elim assump_12
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p2 p0 p6 p5 p7 : Prop)
theorem file42_4915 : (((((p6 ∨ p7) → False) → ((p0 ∨ p6) → False)) → (((p5 → True) ∨ (p7 ∨ False)) ∨ ((True ∧ p5) → (p6 ∨ p2)))) ∨ ((((p0 ∨ True) ∧ (p2 ∧ p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p1 p3 p5 p2 p6 p7 : Prop)
theorem file42_5236 : (((((p2 ∧ p2) ∨ (p2 → False)) → False) → (((p7 ∧ p1) ∨ (True ∧ p7)) → False)) ∨ ((((p5 ∧ p6) ∨ (p6 → False)) ∧ ((p1 → False) → False)) ∧ (((p6 → p5) ∧ (p3 ∨ p1)) ∧ ((p3 → p5) ∨ (True → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_45 : ((p2 ∧ p2) ∨ (p2 → False)) := by
        apply Or.inr
        intro assump_14
        have assump_46 : ((p2 ∧ p2) ∨ (p2 → False)) := by
          apply Or.inl
          apply And.intro
          exact assump_14
          exact assump_14
        let assump_18 := assump_1 assump_46
        apply False.elim assump_18
      let assump_13 := assump_1 assump_45
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case intro assump_25 assump_26 =>
      have assump_47 : ((p2 ∧ p2) ∨ (p2 → False)) := by
        apply Or.inr
        intro assump_34
        have assump_48 : ((p2 ∧ p2) ∨ (p2 → False)) := by
          apply Or.inl
          apply And.intro
          exact assump_34
          exact assump_34
        let assump_38 := assump_1 assump_48
        apply False.elim assump_38
      let assump_33 := assump_1 assump_47
      apply False.elim assump_33


variable (p0 p4 p3 p2 p5 p1 p7 : Prop)
theorem file42_6550 : (((((True ∨ p4) → False) ∧ ((p2 ∧ p7) ∧ (p1 ∨ p5))) → (((p7 ∧ True) → False) ∨ ((p1 ∨ False) → (p4 ∨ p0)))) ∨ ((((p5 → True) ∨ (p5 ∨ p5)) → ((p3 ∧ False) → (True → False))) ∨ (((p5 ∧ p1) → (p2 ∧ p3)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            have assump_50 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_29 := assump_2 assump_50
            apply False.elim assump_29
        case inr assump_15 =>
          apply Or.inl
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            have assump_51 : (True ∨ p4) := by
              apply Or.inl
              apply True.intro
            let assump_46 := assump_2 assump_51
            apply False.elim assump_46


variable (p3 p1 p6 p4 p7 : Prop)
theorem file42_7726 : (((((p6 → False) ∨ (p4 ∧ p3)) ∧ ((p6 → False) → False)) ∧ (((p4 → False) → False) ∧ ((True ∨ p6) → False))) → ((((p1 ∨ p1) ∧ (p7 ∧ p3)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          have assump_43 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_21 := assump_16 assump_43
          apply False.elim assump_21
      case inr assump_10 =>
        cases assump_10
        case intro assump_25 assump_26 =>
          cases assump_6
          case intro assump_33 assump_34 =>
            have assump_44 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_39 := assump_34 assump_44
            apply False.elim assump_39


variable (p4 p3 p7 p6 p2 p5 p1 : Prop)
theorem file42_8742 : (((((True ∧ p6) ∨ (True ∧ p4)) ∧ ((False ∨ True) ∨ (True ∨ p5))) ∨ (((False → p4) ∨ (p7 → False)) ∨ ((p3 ∧ p2) → False))) ∨ ((((p3 → p5) ∧ (p1 → p3)) → ((p5 ∨ p3) → (p3 ∨ p4))) ∨ (((p5 ∨ True) ∨ (p4 → False)) ∧ ((p5 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p4 p5 p2 p3 p6 p0 p7 : Prop)
theorem file42_9150 : (((((p3 ∨ True) → False) ∧ ((p2 ∨ p6) → False)) ∧ (((p0 ∧ p0) → (False → p7)) → ((p4 ∨ p7) → False))) → ((((p4 → p5) ∧ (p6 → p5)) → False) → False)) := by
  intro assump_9
  intro assump_10
  cases assump_9
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      have assump_34 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_30 := assump_15 assump_34
      apply False.elim assump_30


variable (p3 p5 p1 p6 p4 p2 p7 : Prop)
theorem file42_9677 : ((((((p2 → p2) ∧ (False ∧ p7)) ∨ ((True ∨ p7) → False)) → (((p3 ∧ False) ∨ (True ∨ p6)) → ((p1 ∨ p5) ∨ (p6 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p2 → p2) ∧ (False ∧ p7)) ∨ ((True ∨ p7) → False)) → (((p3 ∧ False) ∨ (True ∨ p6)) → ((p1 ∨ p5) ∨ (p6 ∨ p4)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_8
      case inl assump_15 =>
        cases assump_5
        case inl assump_19 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            cases assump_22
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
        case inr assump_20 =>
          have assump_53 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_31 := assump_20 assump_53
          apply False.elim assump_31
      case inr assump_16 =>
        cases assump_5
        case inl assump_37 =>
          cases assump_37
          case intro assump_39 assump_40 =>
            cases assump_40
            case intro assump_43 assump_44 =>
              apply False.elim assump_43
        case inr assump_38 =>
          apply Or.inr
          apply Or.inl
          exact assump_16
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p6 p7 p2 p4 p3 p0 : Prop)
theorem file42_11168 : (((((p2 ∨ p3) → False) ∧ ((p7 ∧ p2) ∧ (False → p6))) → (((p7 → p6) → False) → False)) ∨ ((((p4 ∨ p4) → (p6 ∧ p6)) → False) ∨ (((p2 ∧ p0) → (p4 → p3)) → ((p2 → False) ∨ (p4 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_26 : (p2 ∨ p3) := by
          apply Or.inl
          exact assump_12
        let assump_22 := assump_5 assump_26
        apply False.elim assump_22


variable (p5 p0 p3 p6 p1 p7 p4 : Prop)
theorem file42_11805 : (((((p1 → p6) ∧ (p4 ∨ True)) ∨ ((p0 → p3) ∨ (p4 ∧ p5))) → (((p6 → p0) → False) → ((p1 ∧ p0) → False))) ∨ ((((p6 ∧ p1) ∨ (p3 → False)) → ((True → True) → False)) → (((p3 → False) ∨ (False → False)) ∧ ((p5 → p7) → (p7 → p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          have assump_71 : (p6 → p0) := by
            intro assump_26
            exact assump_5
          let assump_25 := assump_2 assump_71
          apply False.elim assump_25
        case inr assump_19 =>
          have assump_72 : (p6 → p0) := by
            intro assump_37
            exact assump_5
          let assump_36 := assump_2 assump_72
          apply False.elim assump_36
    case inr assump_13 =>
      cases assump_13
      case inl assump_43 =>
        have assump_73 : (p6 → p0) := by
          intro assump_50
          exact assump_5
        let assump_49 := assump_2 assump_73
        apply False.elim assump_49
      case inr assump_44 =>
        cases assump_44
        case intro assump_56 assump_57 =>
          have assump_74 : (p6 → p0) := by
            intro assump_65
            exact assump_5
          let assump_64 := assump_2 assump_74
          apply False.elim assump_64


variable (p0 p1 p3 p6 p2 p7 p5 p4 : Prop)
theorem file42_13295 : (((((p7 → False) → (p4 ∨ p5)) → False) → (((p3 → p6) ∨ (p6 → p1)) → ((p7 ∨ False) → (p0 → p7)))) ∨ ((((False ∨ p1) ∨ (p0 → p7)) ∧ ((True ∨ p2) ∨ (False ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_2
    case inl assump_11 =>
      exact assump_7
    case inr assump_12 =>
      exact assump_7
  case inr assump_8 =>
    apply False.elim assump_8


variable (p0 p7 p6 p3 p1 p5 p2 : Prop)
theorem file42_13823 : ((((((False → p2) → False) → False) ∨ (((p6 → False) ∨ (True ∧ p6)) ∨ ((p7 → p5) ∨ (p0 ∨ False)))) ∧ ((((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_140 : (((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) := by
        intro assump_11
        apply And.intro
        intro assump_12
        cases assump_11
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        apply And.intro
        cases assump_11
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
        apply True.intro
      let assump_10 := assump_3 assump_140
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_30 =>
        cases assump_30
        case inl assump_32 =>
          have assump_141 : (((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) := by
            intro assump_39
            apply And.intro
            intro assump_40
            cases assump_39
            case intro assump_43 assump_44 =>
              cases assump_43
              case intro assump_45 assump_46 =>
                apply False.elim assump_45
            apply And.intro
            cases assump_39
            case intro assump_49 assump_50 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                apply False.elim assump_51
            apply True.intro
          let assump_38 := assump_3 assump_141
          apply False.elim assump_38
        case inr assump_33 =>
          cases assump_33
          case intro assump_58 assump_59 =>
            have assump_142 : (((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) := by
              intro assump_67
              apply And.intro
              intro assump_68
              cases assump_67
              case intro assump_71 assump_72 =>
                cases assump_71
                case intro assump_73 assump_74 =>
                  apply False.elim assump_73
              apply And.intro
              cases assump_67
              case intro assump_77 assump_78 =>
                cases assump_77
                case intro assump_79 assump_80 =>
                  apply False.elim assump_79
              apply True.intro
            let assump_66 := assump_3 assump_142
            apply False.elim assump_66
      case inr assump_31 =>
        cases assump_31
        case inl assump_86 =>
          have assump_143 : (((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) := by
            intro assump_93
            apply And.intro
            intro assump_94
            cases assump_93
            case intro assump_97 assump_98 =>
              cases assump_97
              case intro assump_99 assump_100 =>
                apply False.elim assump_99
            apply And.intro
            cases assump_93
            case intro assump_103 assump_104 =>
              cases assump_103
              case intro assump_105 assump_106 =>
                apply False.elim assump_105
            apply True.intro
          let assump_92 := assump_3 assump_143
          apply False.elim assump_92
        case inr assump_87 =>
          cases assump_87
          case inl assump_112 =>
            have assump_144 : (((False ∧ p2) ∧ (p6 ∧ p2)) → ((p3 → p1) ∧ (p7 ∧ True))) := by
              intro assump_119
              apply And.intro
              intro assump_120
              cases assump_119
              case intro assump_123 assump_124 =>
                cases assump_123
                case intro assump_125 assump_126 =>
                  apply False.elim assump_125
              apply And.intro
              cases assump_119
              case intro assump_129 assump_130 =>
                cases assump_129
                case intro assump_131 assump_132 =>
                  apply False.elim assump_131
              apply True.intro
            let assump_118 := assump_3 assump_144
            apply False.elim assump_118
          case inr assump_113 =>
            apply False.elim assump_113


variable (p6 p2 p7 p1 p0 p5 : Prop)
theorem file42_18206 : (((((True → False) ∧ (True ∧ True)) ∧ ((p6 ∨ p0) → False)) → False) ∨ ((((True ∧ p2) → False) ∨ ((p7 → False) ∧ (p7 ∨ p1))) → (((p1 ∨ p2) → False) → ((p5 ∧ p7) → (p7 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_21 : True := by
          apply True.intro
        let assump_17 := assump_4 assump_21
        apply False.elim assump_17


variable (p4 p2 p1 p0 p6 p5 p3 : Prop)
theorem file42_18790 : (((((p6 → False) → (False → p1)) ∨ ((p1 ∨ p2) ∨ (True ∨ p6))) → False) → ((((p0 → p5) → False) ∨ ((p0 → p5) → (p2 → p4))) ∨ (((p4 → False) → (True → False)) → ((p2 → False) → (p3 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_16 : (((p6 → False) → (False → p1)) ∨ ((p1 ∨ p2) ∨ (True ∨ p6))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_1 assump_16
  apply False.elim assump_8


variable (p3 p7 p4 p1 : Prop)
theorem file42_19343 : ((((((p7 → True) → (True → False)) ∧ ((p4 ∧ p1) → (p3 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 → True) → (True → False)) ∧ ((p4 ∧ p1) → (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_23 : (p7 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_6 assump_23
      have assump_24 : True := by
        apply True.intro
      let assump_15 := assump_13 assump_24
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p1 p6 p5 p3 p2 : Prop)
theorem file42_20021 : (((((True ∧ p6) ∨ (p5 → p1)) ∨ ((p6 → p3) ∨ (p0 → False))) ∨ (((p6 ∧ p2) → False) ∨ ((p6 → p2) → False))) → ((((p0 → False) ∧ (False ∧ True)) → False) ∨ (((False ∧ False) ∨ (p6 ∨ p6)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply Or.inl
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
      case inr assump_7 =>
        apply Or.inl
        intro assump_25
        cases assump_25
        case intro assump_26 assump_27 =>
          cases assump_27
          case intro assump_30 assump_31 =>
            apply False.elim assump_30
    case inr assump_5 =>
      cases assump_5
      case inl assump_34 =>
        apply Or.inl
        intro assump_38
        cases assump_38
        case intro assump_39 assump_40 =>
          cases assump_40
          case intro assump_43 assump_44 =>
            apply False.elim assump_43
      case inr assump_35 =>
        apply Or.inl
        intro assump_49
        cases assump_49
        case intro assump_50 assump_51 =>
          cases assump_51
          case intro assump_54 assump_55 =>
            apply False.elim assump_54
  case inr assump_3 =>
    cases assump_3
    case inl assump_58 =>
      apply Or.inl
      intro assump_62
      cases assump_62
      case intro assump_63 assump_64 =>
        cases assump_64
        case intro assump_67 assump_68 =>
          apply False.elim assump_67
    case inr assump_59 =>
      apply Or.inl
      intro assump_73
      cases assump_73
      case intro assump_74 assump_75 =>
        cases assump_75
        case intro assump_78 assump_79 =>
          apply False.elim assump_78


variable (p7 p5 p6 p1 p3 p2 p0 p4 : Prop)
theorem file42_22029 : ((((((False ∧ p0) ∧ (True → False)) → False) → (((p2 → p7) ∧ (False ∧ p5)) ∧ ((p1 → False) → (False ∧ p3)))) ∧ ((((p6 ∨ p4) → False) ∧ ((p5 → True) ∨ (p2 → p1))) ∧ (((p0 ∧ p1) → (False → False)) ∨ ((p2 ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_7
          case inl assump_16 =>
            have assump_102 : (((False ∧ p0) ∧ (True → False)) → False) := by
              intro assump_24
              cases assump_24
              case intro assump_25 assump_26 =>
                cases assump_25
                case intro assump_27 assump_28 =>
                  apply False.elim assump_27
            let assump_23 := assump_2 assump_102
            let assump_31 := And.left assump_23
            let assump_32 := And.right assump_31
            let assump_34 := And.left assump_32
            apply False.elim assump_34
          case inr assump_17 =>
            have assump_103 : (((False ∧ p0) ∧ (True → False)) → False) := by
              intro assump_44
              cases assump_44
              case intro assump_45 assump_46 =>
                cases assump_45
                case intro assump_47 assump_48 =>
                  apply False.elim assump_47
            let assump_43 := assump_2 assump_103
            let assump_51 := And.left assump_43
            let assump_52 := And.right assump_51
            let assump_54 := And.left assump_52
            apply False.elim assump_54
        case inr assump_13 =>
          cases assump_7
          case inl assump_60 =>
            have assump_104 : (((False ∧ p0) ∧ (True → False)) → False) := by
              intro assump_68
              cases assump_68
              case intro assump_69 assump_70 =>
                cases assump_69
                case intro assump_71 assump_72 =>
                  apply False.elim assump_71
            let assump_67 := assump_2 assump_104
            let assump_75 := And.left assump_67
            let assump_76 := And.right assump_75
            let assump_78 := And.left assump_76
            apply False.elim assump_78
          case inr assump_61 =>
            have assump_105 : (((False ∧ p0) ∧ (True → False)) → False) := by
              intro assump_88
              cases assump_88
              case intro assump_89 assump_90 =>
                cases assump_89
                case intro assump_91 assump_92 =>
                  apply False.elim assump_91
            let assump_87 := assump_2 assump_105
            let assump_95 := And.left assump_87
            let assump_96 := And.right assump_95
            let assump_98 := And.left assump_96
            apply False.elim assump_98


variable (p7 p0 p1 p2 p5 p4 p3 : Prop)
theorem file42_24954 : ((((((p7 ∧ False) → False) ∨ ((p1 → False) → (p2 ∨ p1))) ∨ (((True → p0) → (False ∧ p5)) ∧ ((False → False) ∧ (p2 ∨ False)))) ∧ ((((True → p2) ∨ (p3 → False)) → ((True → False) → False)) ∧ (((p4 → False) ∧ (p3 ∧ False)) ∧ ((p1 ∧ p1) ∧ (p7 ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
      case inr assump_7 =>
        cases assump_3
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              cases assump_35
              case intro assump_38 assump_39 =>
                apply False.elim assump_39
    case inr assump_5 =>
      cases assump_5
      case intro assump_44 assump_45 =>
        cases assump_45
        case intro assump_48 assump_49 =>
          cases assump_49
          case inl assump_52 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              cases assump_57
              case intro assump_60 assump_61 =>
                cases assump_60
                case intro assump_62 assump_63 =>
                  cases assump_63
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_67
          case inr assump_53 =>
            apply False.elim assump_53


variable (p2 p4 p5 p1 p3 : Prop)
theorem file42_26769 : (((((p4 → p1) ∨ (p5 ∨ p2)) ∧ ((p4 → True) → (p3 ∨ p4))) ∧ (((p1 ∧ p1) → (p3 ∨ p1)) → False)) → ((((p5 → False) ∨ (p3 ∨ p3)) → False) ∨ (((p5 → p1) → False) → ((p5 → False) → (p1 ∧ p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_14
        cases assump_14
        case inl assump_15 =>
          have assump_161 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
            intro assump_21
            cases assump_21
            case intro assump_22 assump_23 =>
              apply Or.inr
              exact assump_23
          let assump_20 := assump_3 assump_161
          apply False.elim assump_20
        case inr assump_16 =>
          cases assump_16
          case inl assump_31 =>
            have assump_162 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
              intro assump_37
              cases assump_37
              case intro assump_38 assump_39 =>
                apply Or.inl
                exact assump_31
            let assump_36 := assump_3 assump_162
            apply False.elim assump_36
          case inr assump_32 =>
            have assump_163 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
              intro assump_51
              cases assump_51
              case intro assump_52 assump_53 =>
                apply Or.inl
                exact assump_32
            let assump_50 := assump_3 assump_163
            apply False.elim assump_50
      case inr assump_7 =>
        cases assump_7
        case inl assump_61 =>
          apply Or.inl
          intro assump_69
          cases assump_69
          case inl assump_70 =>
            have assump_164 : p5 := by
              exact assump_61
            let assump_74 := assump_70 assump_164
            apply False.elim assump_74
          case inr assump_71 =>
            cases assump_71
            case inl assump_78 =>
              have assump_165 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
                intro assump_84
                cases assump_84
                case intro assump_85 assump_86 =>
                  apply Or.inl
                  exact assump_78
              let assump_83 := assump_3 assump_165
              apply False.elim assump_83
            case inr assump_79 =>
              have assump_166 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
                intro assump_98
                cases assump_98
                case intro assump_99 assump_100 =>
                  apply Or.inl
                  exact assump_79
              let assump_97 := assump_3 assump_166
              apply False.elim assump_97
        case inr assump_62 =>
          apply Or.inl
          intro assump_114
          cases assump_114
          case inl assump_115 =>
            have assump_167 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
              intro assump_121
              cases assump_121
              case intro assump_122 assump_123 =>
                apply Or.inr
                exact assump_123
            let assump_120 := assump_3 assump_167
            apply False.elim assump_120
          case inr assump_116 =>
            cases assump_116
            case inl assump_131 =>
              have assump_168 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
                intro assump_137
                cases assump_137
                case intro assump_138 assump_139 =>
                  apply Or.inl
                  exact assump_131
              let assump_136 := assump_3 assump_168
              apply False.elim assump_136
            case inr assump_132 =>
              have assump_169 : ((p1 ∧ p1) → (p3 ∨ p1)) := by
                intro assump_151
                cases assump_151
                case intro assump_152 assump_153 =>
                  apply Or.inl
                  exact assump_132
              let assump_150 := assump_3 assump_169
              apply False.elim assump_150


variable (p0 p4 p7 p5 p6 p2 p1 : Prop)
theorem file42_30767 : (((((False → False) → (True → False)) → ((p7 → p7) → False)) ∧ (((p0 ∧ False) ∧ (p4 ∧ p5)) → False)) → ((((False → True) ∨ (False → p0)) ∨ ((p7 ∨ p6) → False)) ∧ (((p7 ∧ p1) → (p2 ∨ p7)) ∨ ((p0 → p6) ∧ (p0 → p4))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    apply True.intro
  cases assump_1
  case intro assump_9 assump_10 =>
    apply Or.inl
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply Or.inr
      exact assump_16


variable (p4 p2 p6 : Prop)
theorem file42_31388 : (((((False ∧ p6) → False) → ((False ∧ p4) → False)) ∧ (((False → False) ∨ (p2 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p2 → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p2 p7 p6 p4 p3 p0 : Prop)
theorem file42_31833 : (((((p1 ∧ p0) ∧ (True ∧ p2)) ∧ ((p6 → p7) → False)) ∧ (((False ∧ p2) → (p1 → p0)) → False)) → ((((p1 ∨ True) → False) ∧ ((p3 → p7) ∨ (p2 → p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              cases assump_16
              case intro assump_23 assump_24 =>
                have assump_81 : ((False ∧ p2) → (p1 → p0)) := by
                  intro assump_34
                  intro assump_35
                  cases assump_34
                  case intro assump_38 assump_39 =>
                    apply False.elim assump_38
                let assump_33 := assump_12 assump_81
                apply False.elim assump_33
    case inr assump_8 =>
      cases assump_1
      case intro assump_47 assump_48 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          cases assump_49
          case intro assump_51 assump_52 =>
            cases assump_51
            case intro assump_53 assump_54 =>
              cases assump_52
              case intro assump_59 assump_60 =>
                have assump_82 : ((False ∧ p2) → (p1 → p0)) := by
                  intro assump_70
                  intro assump_71
                  cases assump_70
                  case intro assump_74 assump_75 =>
                    apply False.elim assump_74
                let assump_69 := assump_48 assump_82
                apply False.elim assump_69


variable (p5 p7 p2 p0 p4 p1 p3 : Prop)
theorem file42_33635 : (((((p3 ∨ p4) ∨ (False ∧ True)) ∧ ((p2 ∧ p2) ∨ (p3 ∧ p4))) ∨ (((False → p2) ∧ (p0 → p0)) ∨ ((p1 ∧ p5) → False))) ∨ ((((p3 → False) ∧ (True → False)) → ((True → p5) ∨ (False ∧ p1))) → (((p0 → False) ∧ (p3 ∨ p7)) → ((p4 → p4) ∧ (p5 → p1))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply And.intro
  intro assump_9
  apply False.elim assump_9
  intro assump_12
  exact assump_12


variable (p0 : Prop)
theorem file42_34070 : (((((True → False) ∧ (p0 → False)) → False) → False) → False) := by
  intro assump_1
  have assump_20 : (((True → False) ∧ (p0 → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_21 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_21
      apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p4 p3 p5 p6 : Prop)
theorem file42_34552 : (((((p0 ∧ p3) → False) ∧ ((False ∧ p5) → False)) ∧ (((p6 ∧ False) → False) → ((True → False) ∧ (False ∨ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_25 : ((p6 ∧ False) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
      let assump_12 := assump_3 assump_25
      let assump_20 := And.left assump_12
      have assump_26 : True := by
        apply True.intro
      let assump_21 := assump_20 assump_26
      apply False.elim assump_21


variable (p7 p3 p4 p0 p6 p5 : Prop)
theorem file42_35259 : (((((p6 ∧ False) → False) ∨ ((False → p3) ∨ (True → False))) ∨ (((p7 → p0) → (p6 ∨ p5)) ∨ ((p6 ∧ True) → False))) ∧ ((((p3 ∨ p5) → (True ∧ True)) ∨ ((p4 ∨ p5) → (p5 → p7))) ∧ (((p3 → True) → False) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  apply And.intro
  apply Or.inl
  intro assump_8
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_9
  have assump_17 : (p3 → True) := by
    intro assump_13
    apply True.intro
  let assump_12 := assump_9 assump_17
  apply False.elim assump_12


variable (p3 p6 p2 p1 p4 p0 p7 p5 : Prop)
theorem file42_35954 : (((((p6 ∧ p5) ∨ (False → False)) ∨ ((p4 → p0) ∨ (True ∨ p2))) ∧ (((p0 ∧ p1) ∧ (p7 ∧ False)) → False)) → ((((p6 → False) ∧ (p4 ∧ p6)) ∧ ((p1 ∨ p3) → False)) → (((False ∧ p3) ∨ (p1 ∨ p5)) ∨ ((p1 → False) ∨ (p0 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                apply Or.inl
                apply Or.inr
                apply Or.inr
                exact assump_24
            case inr assump_22 =>
              apply Or.inr
              apply Or.inl
              intro assump_35
              have assump_91 : (p1 ∨ p3) := by
                apply Or.inl
                exact assump_35
              let assump_41 := assump_4 assump_91
              apply False.elim assump_41
          case inr assump_20 =>
            cases assump_20
            case inl assump_45 =>
              apply Or.inr
              apply Or.inl
              intro assump_51
              have assump_92 : (p1 ∨ p3) := by
                apply Or.inl
                exact assump_51
              let assump_58 := assump_4 assump_92
              apply False.elim assump_58
            case inr assump_46 =>
              cases assump_46
              case inl assump_62 =>
                apply Or.inr
                apply Or.inl
                intro assump_68
                have assump_93 : (p1 ∨ p3) := by
                  apply Or.inl
                  exact assump_68
                let assump_73 := assump_4 assump_93
                apply False.elim assump_73
              case inr assump_63 =>
                apply Or.inr
                apply Or.inl
                intro assump_81
                have assump_94 : (p1 ∨ p3) := by
                  apply Or.inl
                  exact assump_81
                let assump_87 := assump_4 assump_94
                apply False.elim assump_87


variable (p3 p7 p0 p1 p4 p2 : Prop)
theorem file42_38248 : ((((((p0 ∧ p4) → False) → False) ∧ (((p7 → p1) ∧ (p7 ∧ p1)) → False)) ∧ ((((True ∧ False) ∨ (False → False)) → False) ∧ (((False → False) ∧ (p4 ∧ p1)) → ((True ∧ p3) ∨ (p2 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_27 : ((True ∧ False) ∨ (False → False)) := by
          apply Or.inr
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_10 assump_27
        apply False.elim assump_20


variable (p0 p6 p1 p2 p5 p4 p7 : Prop)
theorem file42_38924 : (((((p2 → p2) → (p1 ∧ p0)) → False) ∧ (((p4 ∨ p0) → (p1 ∨ p7)) ∧ ((p5 → p5) ∧ (p0 ∧ p7)))) → ((((p1 → p7) → (False ∨ False)) → ((p1 ∨ p0) ∧ (p6 → False))) ∨ (((p2 ∨ p4) ∧ (p6 ∨ p0)) → ((p4 ∨ p0) ∨ (p4 ∧ False))))) := by
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
          apply And.intro
          apply Or.inr
          exact assump_14
          intro assump_23
          have assump_39 : (p1 → p7) := by
            intro assump_29
            exact assump_15
          let assump_28 := assump_20 assump_39
          cases assump_28
          case inl assump_33 =>
            apply False.elim assump_33
          case inr assump_34 =>
            apply False.elim assump_34


variable (p7 p0 p1 p6 p4 p3 p5 : Prop)
theorem file42_39921 : (((((p6 ∧ False) → False) → ((False ∨ p7) ∧ (p1 → False))) ∧ (((p4 ∨ p7) → False) ∧ ((p5 → False) ∧ (p3 ∧ p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_48 : ((p6 ∧ False) → False) := by
            intro assump_25
            cases assump_25
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
          let assump_24 := assump_2 assump_48
          let assump_32 := And.left assump_24
          cases assump_32
          case inl assump_34 =>
            apply False.elim assump_34
          case inr assump_35 =>
            have assump_49 : (p4 ∨ p7) := by
              apply Or.inr
              exact assump_35
            let assump_44 := assump_6 assump_49
            apply False.elim assump_44


variable (p5 p6 p3 p0 p2 p1 p7 : Prop)
theorem file42_40971 : ((((((p7 → False) → (p0 → p5)) ∨ ((False ∨ p1) → (p1 → False))) → (((True → False) → False) ∧ ((False ∨ p0) ∧ (p3 → p6)))) ∧ ((((p7 → False) ∨ (p2 → False)) → ((False → False) ∨ (p0 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p7 → False) ∨ (p2 → False)) → ((False → False) ∨ (p0 ∧ p6))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      case inr assump_11 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p6 p5 p0 p7 p4 p3 p1 : Prop)
theorem file42_41735 : ((((((p6 ∨ p0) ∧ (p1 ∨ p1)) → ((p7 → p3) ∧ (p4 → p6))) → (((p1 ∨ True) ∨ (p4 ∨ p7)) ∨ ((p4 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 ∨ p0) ∧ (p1 ∨ p1)) → ((p7 → p3) ∧ (p4 → p6))) → (((p1 ∨ True) ∨ (p4 ∨ p7)) ∨ ((p4 → p5) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p0 p6 p7 p5 p3 p1 : Prop)
theorem file42_42234 : (((((p3 → p1) ∧ (False ∧ p5)) → False) → (((True ∨ p3) ∨ (p0 ∨ p6)) ∨ ((p0 ∧ p5) → (p5 → False)))) ∨ ((((True ∨ p2) ∧ (p7 ∧ p5)) ∧ ((True → False) → False)) ∨ (((p6 → False) → (p0 → False)) ∧ ((p3 ∧ p5) ∧ (p7 ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p2 p4 p7 p5 p6 p3 p1 : Prop)
theorem file42_42618 : (((((True → False) → (p4 → p7)) ∨ ((p6 ∧ p5) → (p1 ∨ False))) → False) → ((((p2 → True) ∨ (p3 → p7)) → False) ∨ (((False ∨ False) → (p3 → True)) ∨ ((p3 ∧ False) → (p7 ∨ p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_41 : (((True → False) → (p4 → p7)) ∨ ((p6 ∧ p5) → (p1 ∨ False))) := by
      apply Or.inl
      intro assump_11
      intro assump_12
      have assump_42 : True := by
        apply True.intro
      let assump_17 := assump_11 assump_42
      apply False.elim assump_17
    let assump_10 := assump_1 assump_41
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_43 : (((True → False) → (p4 → p7)) ∨ ((p6 ∧ p5) → (p1 ∨ False))) := by
      apply Or.inl
      intro assump_28
      intro assump_29
      have assump_44 : True := by
        apply True.intro
      let assump_34 := assump_28 assump_44
      apply False.elim assump_34
    let assump_27 := assump_1 assump_43
    apply False.elim assump_27


variable (p5 p0 p4 p3 p7 : Prop)
theorem file42_43682 : ((((((p3 ∧ False) → (p3 → False)) → ((False → p0) → (True → False))) → (((p3 ∨ p4) ∧ (p5 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_114 : ((((p3 ∧ False) → (p3 → False)) → ((False → p0) → (True → False))) → (((p3 ∨ p4) ∧ (p5 ∨ p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          have assump_115 : ((p3 ∧ False) → (p3 → False)) := by
            intro assump_20
            intro assump_21
            cases assump_20
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
          let assump_19 := assump_5 assump_115
          have assump_116 : (False → p0) := by
            intro assump_31
            apply False.elim assump_31
          let assump_30 := assump_19 assump_116
          have assump_117 : True := by
            apply True.intro
          let assump_34 := assump_30 assump_117
          apply False.elim assump_34
        case inr assump_14 =>
          have assump_118 : ((p3 ∧ False) → (p3 → False)) := by
            intro assump_43
            intro assump_44
            cases assump_43
            case intro assump_47 assump_48 =>
              apply False.elim assump_48
          let assump_42 := assump_5 assump_118
          have assump_119 : (False → p0) := by
            intro assump_54
            apply False.elim assump_54
          let assump_53 := assump_42 assump_119
          have assump_120 : True := by
            apply True.intro
          let assump_57 := assump_53 assump_120
          apply False.elim assump_57
      case inr assump_10 =>
        cases assump_8
        case inl assump_63 =>
          have assump_121 : ((p3 ∧ False) → (p3 → False)) := by
            intro assump_70
            intro assump_71
            cases assump_70
            case intro assump_74 assump_75 =>
              apply False.elim assump_75
          let assump_69 := assump_5 assump_121
          have assump_122 : (False → p0) := by
            intro assump_81
            apply False.elim assump_81
          let assump_80 := assump_69 assump_122
          have assump_123 : True := by
            apply True.intro
          let assump_84 := assump_80 assump_123
          apply False.elim assump_84
        case inr assump_64 =>
          have assump_124 : ((p3 ∧ False) → (p3 → False)) := by
            intro assump_93
            intro assump_94
            cases assump_93
            case intro assump_97 assump_98 =>
              apply False.elim assump_98
          let assump_92 := assump_5 assump_124
          have assump_125 : (False → p0) := by
            intro assump_104
            apply False.elim assump_104
          let assump_103 := assump_92 assump_125
          have assump_126 : True := by
            apply True.intro
          let assump_107 := assump_103 assump_126
          apply False.elim assump_107
  let assump_4 := assump_1 assump_114
  apply False.elim assump_4


variable (p0 : Prop)
theorem file42_46799 : (((((False → p0) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p0) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p0) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p0 p7 p3 p6 p2 p1 : Prop)
theorem file42_47242 : (((((p3 ∨ p6) ∧ (p7 → p3)) ∨ ((p7 ∧ False) ∨ (True → p5))) → (((p0 → p6) → (p1 ∨ True)) ∨ ((p2 → True) → (True ∨ p1)))) ∨ ((((p0 → False) → False) → ((p6 → False) ∨ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_12
        apply Or.inr
        apply True.intro
      case inr assump_7 =>
        apply Or.inl
        intro assump_19
        apply Or.inr
        apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_22 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply False.elim assump_25
    case inr assump_23 =>
      apply Or.inl
      intro assump_32
      apply Or.inr
      apply True.intro


variable (p4 p6 p5 p1 : Prop)
theorem file42_48150 : ((((((True ∨ p6) → False) → False) ∨ (((p5 → p4) → False) ∧ ((p1 ∧ True) → (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p6) → False) → False) ∨ (((p5 → p4) → False) ∧ ((p1 ∧ True) → (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p6 p2 p1 p0 p4 : Prop)
theorem file42_48707 : (((((p1 ∨ p3) → (p1 ∨ p3)) ∧ ((p6 → False) ∨ (True → False))) → (((p6 ∨ p6) ∧ (p4 → False)) → False)) ∨ ((((p2 → False) ∨ (p4 ∧ p0)) ∨ ((p0 → False) → (False → False))) ∨ (((True ∧ p6) → (False → False)) ∧ ((p2 ∧ p6) ∧ (False ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          have assump_51 : p6 := by
            exact assump_5
          let assump_19 := assump_15 assump_51
          apply False.elim assump_19
        case inr assump_16 =>
          have assump_52 : True := by
            apply True.intro
          let assump_25 := assump_16 assump_52
          apply False.elim assump_25
    case inr assump_6 =>
      cases assump_1
      case intro assump_33 assump_34 =>
        cases assump_34
        case inl assump_37 =>
          have assump_53 : p6 := by
            exact assump_6
          let assump_41 := assump_37 assump_53
          apply False.elim assump_41
        case inr assump_38 =>
          have assump_54 : True := by
            apply True.intro
          let assump_47 := assump_38 assump_54
          apply False.elim assump_47


variable (p1 p5 p6 p2 : Prop)
theorem file42_50058 : ((((((p6 ∧ p5) ∧ (p6 → p1)) → False) → (((True → False) ∧ (p2 ∧ p1)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p6 ∧ p5) ∧ (p6 → p1)) → False) → (((True → False) ∧ (p2 ∧ p1)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_30 : True := by
          apply True.intro
        let assump_22 := assump_7 assump_30
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p3 p2 p6 p4 p5 p0 p1 : Prop)
theorem file42_50707 : ((((((p0 → False) ∨ (p5 ∧ p5)) → ((p1 ∧ False) ∨ (False → p3))) ∨ (((p4 ∧ p4) → (p4 ∧ p7)) → ((p2 ∧ p6) ∨ (p6 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p0 → False) ∨ (p5 ∧ p5)) → ((p1 ∧ False) ∨ (False → p3))) ∨ (((p4 ∧ p4) → (p4 ∧ p7)) → ((p2 ∧ p6) ∨ (p6 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_13 assump_14 =>
        apply Or.inr
        intro assump_19
        apply False.elim assump_19
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p6 p7 p5 p2 p4 p3 : Prop)
theorem file42_51463 : (((((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) → (((False ∨ True) ∨ (False → p5)) → False)) → ((((p0 → False) ∨ (p0 ∨ p4)) ∧ ((p7 ∨ p2) ∨ (p3 ∧ p3))) ∧ (((p3 ∨ True) → (False ∧ p5)) ∧ ((p5 → p7) ∨ (True ∨ p6))))) := by
  intro assump_12
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_15
  have assump_111 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
    apply Or.inl
    intro assump_20
    intro assump_21
    apply False.elim assump_21
  let assump_19 := assump_12 assump_111
  have assump_112 : ((False ∨ True) ∨ (False → p5)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_24 := assump_19 assump_112
  apply False.elim assump_24
  have assump_113 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
    apply Or.inl
    intro assump_31
    intro assump_32
    apply False.elim assump_32
  let assump_30 := assump_12 assump_113
  have assump_114 : ((False ∨ True) ∨ (False → p5)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_35 := assump_30 assump_114
  apply False.elim assump_35
  apply And.intro
  intro assump_39
  apply And.intro
  cases assump_39
  case inl assump_40 =>
    have assump_115 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
      apply Or.inl
      intro assump_47
      intro assump_48
      apply False.elim assump_48
    let assump_46 := assump_12 assump_115
    have assump_116 : ((False ∨ True) ∨ (False → p5)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_51 := assump_46 assump_116
    apply False.elim assump_51
  case inr assump_41 =>
    have assump_117 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
      apply Or.inl
      intro assump_60
      intro assump_61
      apply False.elim assump_61
    let assump_59 := assump_12 assump_117
    have assump_118 : ((False ∨ True) ∨ (False → p5)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_64 := assump_59 assump_118
    apply False.elim assump_64
  cases assump_39
  case inl assump_68 =>
    have assump_119 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
      apply Or.inl
      intro assump_75
      intro assump_76
      apply False.elim assump_76
    let assump_74 := assump_12 assump_119
    have assump_120 : ((False ∨ True) ∨ (False → p5)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_79 := assump_74 assump_120
    apply False.elim assump_79
  case inr assump_69 =>
    have assump_121 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
      apply Or.inl
      intro assump_88
      intro assump_89
      apply False.elim assump_89
    let assump_87 := assump_12 assump_121
    have assump_122 : ((False ∨ True) ∨ (False → p5)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_92 := assump_87 assump_122
    apply False.elim assump_92
  apply Or.inl
  intro assump_98
  have assump_123 : (((p6 ∧ p0) → (False → False)) ∨ ((p3 → p7) ∨ (p2 → False))) := by
    apply Or.inl
    intro assump_103
    intro assump_104
    apply False.elim assump_104
  let assump_102 := assump_12 assump_123
  have assump_124 : ((False ∨ True) ∨ (False → p5)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_107 := assump_102 assump_124
  apply False.elim assump_107


variable (p6 p3 p4 p7 p5 p0 p1 : Prop)
theorem file42_54949 : ((((((p5 ∧ p4) ∧ (p0 → p1)) ∧ ((p1 ∨ True) ∨ (p6 → p6))) → (((p3 ∨ p6) ∨ (p6 ∨ p7)) → ((p5 → False) ∨ (p5 → False)))) ∧ ((((p4 → p4) ∨ (p7 → False)) → ((p7 ∧ p7) → (False → p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p4 → p4) ∨ (p7 → False)) → ((p7 ∧ p7) → (False → p6))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p6 p7 p4 p1 p5 : Prop)
theorem file42_55530 : ((((((p4 → False) ∨ (p7 → False)) ∨ ((True ∨ False) → False)) → (((p5 → False) ∧ (True → False)) → ((p5 → False) ∧ (p1 → p6)))) → False) → False) := by
  intro assump_1
  have assump_76 : ((((p4 → False) ∨ (p7 → False)) ∨ ((True ∨ False) → False)) → (((p5 → False) ∧ (True → False)) → ((p5 → False) ∧ (p1 → p6)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          have assump_77 : True := by
            apply True.intro
          let assump_23 := assump_11 assump_77
          apply False.elim assump_23
        case inr assump_19 =>
          have assump_78 : True := by
            apply True.intro
          let assump_30 := assump_11 assump_78
          apply False.elim assump_30
      case inr assump_17 =>
        have assump_79 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_36 := assump_17 assump_79
        apply False.elim assump_36
    intro assump_40
    cases assump_6
    case intro assump_43 assump_44 =>
      cases assump_5
      case inl assump_49 =>
        cases assump_49
        case inl assump_51 =>
          have assump_80 : True := by
            apply True.intro
          let assump_56 := assump_44 assump_80
          apply False.elim assump_56
        case inr assump_52 =>
          have assump_81 : True := by
            apply True.intro
          let assump_63 := assump_44 assump_81
          apply False.elim assump_63
      case inr assump_50 =>
        have assump_82 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_69 := assump_50 assump_82
        apply False.elim assump_69
  let assump_4 := assump_1 assump_76
  apply False.elim assump_4


variable (p1 p0 p3 p5 p6 p2 : Prop)
theorem file42_57464 : ((((((False ∧ p2) → (p0 → False)) ∨ ((p6 ∨ p5) ∧ (p1 ∧ p0))) → False) ∧ ((((False ∧ p2) ∨ (False → False)) ∧ ((p3 ∨ p0) → False)) ∨ (((p2 ∧ p3) ∧ (True ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_11 =>
          have assump_49 : (((False ∧ p2) → (p0 → False)) ∨ ((p6 ∨ p5) ∧ (p1 ∧ p0))) := by
            apply Or.inl
            intro assump_23
            intro assump_24
            cases assump_23
            case intro assump_27 assump_28 =>
              apply False.elim assump_27
          let assump_22 := assump_2 assump_49
          apply False.elim assump_22
    case inr assump_7 =>
      have assump_50 : (((False ∧ p2) → (p0 → False)) ∨ ((p6 ∨ p5) ∧ (p1 ∧ p0))) := by
        apply Or.inl
        intro assump_38
        intro assump_39
        cases assump_38
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      let assump_37 := assump_2 assump_50
      apply False.elim assump_37


variable (p4 p1 p5 : Prop)
theorem file42_58792 : (((((p4 ∧ p1) → False) → ((p4 ∧ False) → (p4 → p5))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p4 ∧ p1) → False) → ((p4 ∧ False) → (p4 → p5))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p2 p7 : Prop)
theorem file42_59225 : ((((((False ∧ False) → (True ∨ p2)) → False) → (((p7 → p4) → (p7 → False)) → False)) → False) → False) := by
  intro assump_14
  have assump_36 : ((((False ∧ False) → (True ∨ p2)) → False) → (((p7 → p4) → (p7 → False)) → False)) := by
    intro assump_18
    intro assump_19
    have assump_37 : ((False ∧ False) → (True ∨ p2)) := by
      intro assump_25
      cases assump_25
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
    let assump_24 := assump_18 assump_37
    apply False.elim assump_24
  let assump_17 := assump_14 assump_36
  apply False.elim assump_17


variable (p6 p5 p1 p3 : Prop)
theorem file42_59872 : ((((((p3 → False) → (p3 → False)) ∨ ((p3 ∨ True) → False)) ∨ (((True → False) ∨ (p5 → True)) ∧ ((p1 ∨ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 → False) → (p3 → False)) ∨ ((p3 ∨ True) → False)) ∨ (((True → False) ∨ (p5 → True)) ∧ ((p1 ∨ p6) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : p3 := by
      exact assump_6
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p2 p4 p1 p6 p5 p7 : Prop)
theorem file42_60492 : ((((((p3 → False) ∧ (p1 ∧ False)) → ((p2 → False) → False)) ∨ (((p6 ∧ False) → (p5 → False)) ∨ ((p4 ∨ p4) → (p7 ∨ p6)))) → False) → False) := by
  intro assump_10
  have assump_31 : ((((p3 → False) ∧ (p1 ∧ False)) → ((p2 → False) → False)) ∨ (((p6 ∧ False) → (p5 → False)) ∨ ((p4 ∨ p4) → (p7 ∨ p6)))) := by
    apply Or.inl
    intro assump_14
    intro assump_15
    cases assump_14
    case intro assump_18 assump_19 =>
      cases assump_19
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  let assump_13 := assump_10 assump_31
  apply False.elim assump_13


variable (p1 p0 p3 p7 p4 p2 p6 : Prop)
theorem file42_61142 : ((((((p0 ∧ p4) → (p7 → p7)) ∨ ((p1 → p2) ∧ (False → p1))) ∨ (((p7 → p0) ∨ (p4 ∧ True)) ∧ ((p3 → False) ∨ (p6 → p2)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∧ p4) → (p7 → p7)) ∨ ((p1 → p2) ∧ (False → p1))) ∨ (((p7 → p0) ∨ (p4 ∧ True)) ∧ ((p3 → False) ∨ (p6 → p2)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 p1 p3 p7 p2 p5 : Prop)
theorem file42_61719 : (((((p6 ∨ p2) → False) → ((p0 ∧ p0) ∨ (p2 → False))) ∨ (((p6 ∨ p5) → (p5 → p0)) → ((p1 ∧ p6) ∧ (p7 ∧ p1)))) ∨ ((((p1 ∨ p5) → False) → ((p3 ∨ p0) → (True ∧ p5))) ∧ (((p6 ∧ True) ∨ (p3 → p3)) → ((p2 ∧ p5) ∨ (p2 → p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  have assump_12 : (p6 ∨ p2) := by
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p4 p5 p2 p7 p3 : Prop)
theorem file42_62216 : ((((((p2 ∧ True) → False) ∧ ((p5 ∨ p2) ∧ (p4 ∨ p5))) → (((p2 ∧ False) → (p3 ∨ p7)) → ((p3 ∧ True) → (False → p5)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p2 ∧ True) → False) ∧ ((p5 ∨ p2) ∧ (p4 ∨ p5))) → (((p2 ∧ False) → (p3 ∨ p7)) → ((p3 ∧ True) → (False → p5)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p2 p5 p3 p1 p0 p4 : Prop)
theorem file42_62746 : (((((True ∧ p7) ∧ (p1 → True)) ∨ ((False ∧ p0) → False)) ∨ (((p7 → False) → False) → False)) ∨ ((((p7 ∨ p7) ∧ (p0 ∧ p0)) ∧ ((p5 → p5) ∨ (True → False))) → (((p2 ∨ True) ∨ (True ∧ p0)) ∧ ((p4 → False) ∧ (p3 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2


variable (p1 p6 p4 p3 p0 : Prop)
theorem file42_63168 : (((((False ∧ p3) ∧ (True ∧ p4)) ∧ ((p0 ∧ p6) ∨ (p6 ∧ p1))) ∧ (((p6 ∨ True) → False) ∨ ((False → True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p2 p1 p7 p0 p6 p5 : Prop)
theorem file42_63637 : ((((((p0 → False) ∧ (p1 ∧ p0)) ∧ ((True ∨ True) → (p2 ∧ p0))) ∨ (((p5 ∧ p2) ∧ (p5 ∨ p0)) ∧ ((p2 → False) → False))) ∧ ((((p0 → False) → (p7 → p5)) → ((p5 ∧ p5) → False)) ∧ (((p2 ∨ p2) ∨ (False ∧ p7)) ∧ ((False → p6) → (p1 → p6))))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_22
          case intro assump_25 assump_26 =>
            cases assump_16
            case intro assump_33 assump_34 =>
              cases assump_34
              case intro assump_37 assump_38 =>
                cases assump_37
                case inl assump_39 =>
                  cases assump_39
                  case inl assump_41 =>
                    have assump_245 : p0 := by
                      exact assump_26
                    let assump_72 := assump_21 assump_245
                    apply False.elim assump_72
                  case inr assump_42 =>
                    have assump_246 : p0 := by
                      exact assump_26
                    let assump_105 := assump_21 assump_246
                    apply False.elim assump_105
                case inr assump_40 =>
                  cases assump_40
                  case intro assump_109 assump_110 =>
                    apply False.elim assump_109
    case inr assump_18 =>
      cases assump_18
      case intro assump_113 assump_114 =>
        cases assump_113
        case intro assump_115 assump_116 =>
          cases assump_115
          case intro assump_117 assump_118 =>
            cases assump_116
            case inl assump_123 =>
              cases assump_16
              case intro assump_129 assump_130 =>
                cases assump_130
                case intro assump_133 assump_134 =>
                  cases assump_133
                  case inl assump_135 =>
                    cases assump_135
                    case inl assump_137 =>
                      have assump_247 : ((p0 → False) → (p7 → p5)) := by
                        intro assump_150
                        intro assump_151
                        exact assump_123
                      let assump_149 := assump_129 assump_247
                      have assump_248 : (p5 ∧ p5) := by
                        apply And.intro
                        exact assump_123
                        exact assump_123
                      let assump_156 := assump_149 assump_248
                      apply False.elim assump_156
                    case inr assump_138 =>
                      have assump_249 : ((p0 → False) → (p7 → p5)) := by
                        intro assump_171
                        intro assump_172
                        exact assump_123
                      let assump_170 := assump_129 assump_249
                      have assump_250 : (p5 ∧ p5) := by
                        apply And.intro
                        exact assump_123
                        exact assump_123
                      let assump_177 := assump_170 assump_250
                      apply False.elim assump_177
                  case inr assump_136 =>
                    cases assump_136
                    case intro assump_181 assump_182 =>
                      apply False.elim assump_181
            case inr assump_124 =>
              cases assump_16
              case intro assump_189 assump_190 =>
                cases assump_190
                case intro assump_193 assump_194 =>
                  cases assump_193
                  case inl assump_195 =>
                    cases assump_195
                    case inl assump_197 =>
                      have assump_251 : ((p0 → False) → (p7 → p5)) := by
                        intro assump_210
                        intro assump_211
                        exact assump_117
                      let assump_209 := assump_189 assump_251
                      have assump_252 : (p5 ∧ p5) := by
                        apply And.intro
                        exact assump_117
                        exact assump_117
                      let assump_216 := assump_209 assump_252
                      apply False.elim assump_216
                    case inr assump_198 =>
                      have assump_253 : ((p0 → False) → (p7 → p5)) := by
                        intro assump_231
                        intro assump_232
                        exact assump_117
                      let assump_230 := assump_189 assump_253
                      have assump_254 : (p5 ∧ p5) := by
                        apply And.intro
                        exact assump_117
                        exact assump_117
                      let assump_237 := assump_230 assump_254
                      apply False.elim assump_237
                  case inr assump_196 =>
                    cases assump_196
                    case intro assump_241 assump_242 =>
                      apply False.elim assump_241


variable (p3 p2 p5 p6 p0 p1 : Prop)
theorem file42_68771 : ((((((p5 ∧ p6) → False) → False) → (((p5 ∨ True) → False) ∧ ((p2 → p3) ∨ (p0 → p1)))) ∧ ((((p0 ∨ p5) → False) → ((True ∨ p3) ∨ (False ∧ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p0 ∨ p5) → False) → ((True ∨ p3) ∨ (False ∧ p1))) := by
      intro assump_9
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p5 p7 p6 p4 p1 p2 p0 : Prop)
theorem file42_69300 : ((((((p4 ∧ p6) → False) ∧ ((True → False) ∧ (p0 ∧ False))) ∧ (((p7 → p7) ∨ (p0 ∨ False)) ∧ ((p1 ∧ p7) → (p6 → p6)))) ∨ ((((False ∨ True) → False) → False) ∧ (((p2 → False) → (p5 ∨ p0)) ∧ ((False → False) ∧ (True ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            apply False.elim assump_33


variable (p3 p0 p7 p2 : Prop)
theorem file42_70256 : ((((((p3 → False) → False) → ((False ∧ p2) → False)) ∨ (((p3 → p7) → False) ∧ ((p3 → p0) ∧ (p2 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → False) → False) → ((False ∧ p2) → False)) ∨ (((p3 → p7) → False) ∧ ((p3 → p0) ∧ (p2 ∧ p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p6 p7 : Prop)
theorem file42_70786 : ((((((p7 ∨ True) ∨ (p2 ∨ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p7 ∨ True) ∨ (p2 ∨ p6)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p7 ∨ True) ∨ (p2 ∨ p6)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p2 p4 p0 p5 p3 p7 p1 : Prop)
theorem file42_71279 : (((((True → False) ∧ (p1 → p1)) → ((p6 ∧ p4) ∨ (p0 → True))) → False) → ((((p2 ∨ p4) → False) → False) ∧ (((p3 ∧ p7) ∧ (p0 ∨ p5)) → False))) := by
  intro assump_24
  apply And.intro
  intro assump_25
  have assump_85 : (((True → False) ∧ (p1 → p1)) → ((p6 ∧ p4) ∨ (p0 → True))) := by
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply Or.inr
      intro assump_38
      apply True.intro
  let assump_30 := assump_24 assump_85
  apply False.elim assump_30
  intro assump_42
  cases assump_42
  case intro assump_43 assump_44 =>
    cases assump_43
    case intro assump_45 assump_46 =>
      cases assump_44
      case inl assump_51 =>
        have assump_86 : (((True → False) ∧ (p1 → p1)) → ((p6 ∧ p4) ∨ (p0 → True))) := by
          intro assump_58
          cases assump_58
          case intro assump_59 assump_60 =>
            apply Or.inr
            intro assump_65
            apply True.intro
        let assump_57 := assump_24 assump_86
        apply False.elim assump_57
      case inr assump_52 =>
        have assump_87 : (((True → False) ∧ (p1 → p1)) → ((p6 ∧ p4) ∨ (p0 → True))) := by
          intro assump_74
          cases assump_74
          case intro assump_75 assump_76 =>
            apply Or.inr
            intro assump_81
            apply True.intro
        let assump_73 := assump_24 assump_87
        apply False.elim assump_73


variable (p1 p2 p3 p4 p6 : Prop)
theorem file42_72735 : (((((p2 ∧ p3) → False) ∧ ((p1 ∧ False) ∧ (p3 → False))) ∧ (((p3 ∧ p3) ∨ (p6 → p2)) ∨ ((p4 → p3) ∨ (p3 ∨ p6)))) → False) := by
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


variable (p4 p0 p3 p1 : Prop)
theorem file42_73199 : (((((True → True) ∨ (p1 → False)) → False) ∨ (((p4 ∧ p3) → (p0 → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_27 : ((True → True) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_7
      apply True.intro
    let assump_6 := assump_2 assump_27
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_28 : ((p4 ∧ p3) → (p0 → p0)) := by
      intro assump_14
      intro assump_15
      cases assump_14
      case intro assump_18 assump_19 =>
        exact assump_15
    let assump_13 := assump_3 assump_28
    apply False.elim assump_13


variable (p4 p5 p0 p3 p2 p1 : Prop)
theorem file42_73876 : (((((p0 ∨ True) → False) → False) → False) → ((((p1 → False) → (p2 → False)) ∨ ((p5 → False) → False)) → (((p2 ∨ p3) ∧ (True ∨ p4)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case inl assump_10 =>
        cases assump_2
        case inl assump_14 =>
          have assump_152 : (((p0 ∨ True) → False) → False) := by
            intro assump_21
            have assump_153 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_24 := assump_21 assump_153
            apply False.elim assump_24
          let assump_20 := assump_1 assump_152
          apply False.elim assump_20
        case inr assump_15 =>
          have assump_154 : (((p0 ∨ True) → False) → False) := by
            intro assump_36
            have assump_155 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_39 := assump_36 assump_155
            apply False.elim assump_39
          let assump_35 := assump_1 assump_154
          apply False.elim assump_35
      case inr assump_11 =>
        cases assump_2
        case inl assump_48 =>
          have assump_156 : (((p0 ∨ True) → False) → False) := by
            intro assump_55
            have assump_157 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_58 := assump_55 assump_157
            apply False.elim assump_58
          let assump_54 := assump_1 assump_156
          apply False.elim assump_54
        case inr assump_49 =>
          have assump_158 : (((p0 ∨ True) → False) → False) := by
            intro assump_70
            have assump_159 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_73 := assump_70 assump_159
            apply False.elim assump_73
          let assump_69 := assump_1 assump_158
          apply False.elim assump_69
    case inr assump_7 =>
      cases assump_5
      case inl assump_82 =>
        cases assump_2
        case inl assump_86 =>
          have assump_160 : (((p0 ∨ True) → False) → False) := by
            intro assump_93
            have assump_161 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_96 := assump_93 assump_161
            apply False.elim assump_96
          let assump_92 := assump_1 assump_160
          apply False.elim assump_92
        case inr assump_87 =>
          have assump_162 : (((p0 ∨ True) → False) → False) := by
            intro assump_108
            have assump_163 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_111 := assump_108 assump_163
            apply False.elim assump_111
          let assump_107 := assump_1 assump_162
          apply False.elim assump_107
      case inr assump_83 =>
        cases assump_2
        case inl assump_120 =>
          have assump_164 : (((p0 ∨ True) → False) → False) := by
            intro assump_127
            have assump_165 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_130 := assump_127 assump_165
            apply False.elim assump_130
          let assump_126 := assump_1 assump_164
          apply False.elim assump_126
        case inr assump_121 =>
          have assump_166 : (((p0 ∨ True) → False) → False) := by
            intro assump_142
            have assump_167 : (p0 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_145 := assump_142 assump_167
            apply False.elim assump_145
          let assump_141 := assump_1 assump_166
          apply False.elim assump_141


variable (p3 p4 p0 p1 p5 p6 p7 : Prop)
theorem file42_77749 : ((((((p0 → p1) ∧ (p6 ∨ p0)) ∨ ((p7 → p7) → (False → p1))) → (((p4 → False) → False) ∨ ((True → False) → (p1 ∧ p5)))) ∧ ((((p7 ∨ p5) → (p4 → p5)) → ((False → False) ∨ (p1 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p7 ∨ p5) → (p4 → p5)) → ((False → False) ∨ (p1 → p3))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p2 p0 p6 p3 p4 p7 p1 p5 : Prop)
theorem file42_78335 : (((((p5 → p2) ∧ (True ∨ False)) → False) ∨ (((p4 ∨ False) → (p5 ∧ p6)) ∨ ((p1 ∧ p1) ∧ (p3 ∧ p4)))) → ((((p4 ∨ p4) → False) ∨ ((p7 → p6) ∨ (p7 ∧ p3))) → (((False → False) ∧ (p0 → False)) → ((False → False) ∧ (True → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  apply True.intro


variable (p0 p3 p4 p7 p5 p1 p6 p2 : Prop)
theorem file42_78782 : (((((True ∧ p2) ∨ (p0 ∨ p7)) → ((False → p5) ∨ (p1 ∨ p0))) ∧ (((False → False) ∨ (p7 ∧ p7)) → ((p0 ∧ p4) → (True → p4)))) ∨ ((((p6 → False) → False) ∧ ((p0 → False) ∧ (True ∧ p1))) ∨ (((p3 → False) ∧ (p5 ∨ p3)) → ((p5 → p6) ∨ (p2 → p0))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inl
      intro assump_17
      apply False.elim assump_17
    case inr assump_14 =>
      apply Or.inl
      intro assump_22
      apply False.elim assump_22
  intro assump_25
  intro assump_26
  intro assump_27
  cases assump_26
  case intro assump_30 assump_31 =>
    cases assump_25
    case inl assump_36 =>
      exact assump_31
    case inr assump_37 =>
      cases assump_37
      case intro assump_40 assump_41 =>
        exact assump_31


variable (p2 p5 p6 p4 p7 p0 p1 p3 : Prop)
theorem file42_79843 : (((((True ∨ p7) → (p3 ∨ p3)) → False) → (((p5 ∨ p4) ∧ (p4 ∧ p5)) → ((False → False) ∨ (p6 → False)))) ∧ ((((p2 → True) ∧ (p0 ∧ True)) ∨ ((p1 ∧ p1) → (p1 ∨ p1))) ∨ (((p5 → False) → (p2 ∧ p7)) ∨ ((p2 → False) ∧ (p3 → p2))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
    case inr assump_6 =>
      cases assump_4
      case intro assump_22 assump_23 =>
        apply Or.inl
        intro assump_30
        apply False.elim assump_30
  apply Or.inl
  apply Or.inr
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    apply Or.inl
    exact assump_36


variable (p2 p5 p7 p3 p0 p4 p6 p1 : Prop)
theorem file42_80730 : ((((((p1 ∨ p7) ∨ (p4 ∧ True)) ∨ ((False ∨ False) → (p3 → False))) ∨ (((p5 → False) ∧ (p5 ∨ p1)) ∨ ((p7 → False) ∧ (p7 → False)))) ∧ ((((p3 ∨ p0) → (p0 ∧ p0)) ∨ ((p5 ∨ p5) ∧ (p3 ∧ True))) ∧ (((p5 → p1) ∨ (p2 → p7)) ∧ ((p2 ∧ False) ∧ (p6 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_3
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_15
                case intro assump_20 assump_21 =>
                  cases assump_20
                  case inl assump_22 =>
                    cases assump_21
                    case intro assump_26 assump_27 =>
                      cases assump_26
                      case intro assump_28 assump_29 =>
                        apply False.elim assump_29
                  case inr assump_23 =>
                    cases assump_21
                    case intro assump_36 assump_37 =>
                      cases assump_36
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_39
              case inr assump_17 =>
                cases assump_17
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case inl assump_46 =>
                    cases assump_45
                    case intro assump_50 assump_51 =>
                      cases assump_15
                      case intro assump_56 assump_57 =>
                        cases assump_56
                        case inl assump_58 =>
                          cases assump_57
                          case intro assump_62 assump_63 =>
                            cases assump_62
                            case intro assump_64 assump_65 =>
                              apply False.elim assump_65
                        case inr assump_59 =>
                          cases assump_57
                          case intro assump_72 assump_73 =>
                            cases assump_72
                            case intro assump_74 assump_75 =>
                              apply False.elim assump_75
                  case inr assump_47 =>
                    cases assump_45
                    case intro assump_82 assump_83 =>
                      cases assump_15
                      case intro assump_88 assump_89 =>
                        cases assump_88
                        case inl assump_90 =>
                          cases assump_89
                          case intro assump_94 assump_95 =>
                            cases assump_94
                            case intro assump_96 assump_97 =>
                              apply False.elim assump_97
                        case inr assump_91 =>
                          cases assump_89
                          case intro assump_104 assump_105 =>
                            cases assump_104
                            case intro assump_106 assump_107 =>
                              apply False.elim assump_107
          case inr assump_11 =>
            cases assump_3
            case intro assump_114 assump_115 =>
              cases assump_114
              case inl assump_116 =>
                cases assump_115
                case intro assump_120 assump_121 =>
                  cases assump_120
                  case inl assump_122 =>
                    cases assump_121
                    case intro assump_126 assump_127 =>
                      cases assump_126
                      case intro assump_128 assump_129 =>
                        apply False.elim assump_129
                  case inr assump_123 =>
                    cases assump_121
                    case intro assump_136 assump_137 =>
                      cases assump_136
                      case intro assump_138 assump_139 =>
                        apply False.elim assump_139
              case inr assump_117 =>
                cases assump_117
                case intro assump_144 assump_145 =>
                  cases assump_144
                  case inl assump_146 =>
                    cases assump_145
                    case intro assump_150 assump_151 =>
                      cases assump_115
                      case intro assump_156 assump_157 =>
                        cases assump_156
                        case inl assump_158 =>
                          cases assump_157
                          case intro assump_162 assump_163 =>
                            cases assump_162
                            case intro assump_164 assump_165 =>
                              apply False.elim assump_165
                        case inr assump_159 =>
                          cases assump_157
                          case intro assump_172 assump_173 =>
                            cases assump_172
                            case intro assump_174 assump_175 =>
                              apply False.elim assump_175
                  case inr assump_147 =>
                    cases assump_145
                    case intro assump_182 assump_183 =>
                      cases assump_115
                      case intro assump_188 assump_189 =>
                        cases assump_188
                        case inl assump_190 =>
                          cases assump_189
                          case intro assump_194 assump_195 =>
                            cases assump_194
                            case intro assump_196 assump_197 =>
                              apply False.elim assump_197
                        case inr assump_191 =>
                          cases assump_189
                          case intro assump_204 assump_205 =>
                            cases assump_204
                            case intro assump_206 assump_207 =>
                              apply False.elim assump_207
        case inr assump_9 =>
          cases assump_9
          case intro assump_212 assump_213 =>
            cases assump_3
            case intro assump_218 assump_219 =>
              cases assump_218
              case inl assump_220 =>
                cases assump_219
                case intro assump_224 assump_225 =>
                  cases assump_224
                  case inl assump_226 =>
                    cases assump_225
                    case intro assump_230 assump_231 =>
                      cases assump_230
                      case intro assump_232 assump_233 =>
                        apply False.elim assump_233
                  case inr assump_227 =>
                    cases assump_225
                    case intro assump_240 assump_241 =>
                      cases assump_240
                      case intro assump_242 assump_243 =>
                        apply False.elim assump_243
              case inr assump_221 =>
                cases assump_221
                case intro assump_248 assump_249 =>
                  cases assump_248
                  case inl assump_250 =>
                    cases assump_249
                    case intro assump_254 assump_255 =>
                      cases assump_219
                      case intro assump_260 assump_261 =>
                        cases assump_260
                        case inl assump_262 =>
                          cases assump_261
                          case intro assump_266 assump_267 =>
                            cases assump_266
                            case intro assump_268 assump_269 =>
                              apply False.elim assump_269
                        case inr assump_263 =>
                          cases assump_261
                          case intro assump_276 assump_277 =>
                            cases assump_276
                            case intro assump_278 assump_279 =>
                              apply False.elim assump_279
                  case inr assump_251 =>
                    cases assump_249
                    case intro assump_286 assump_287 =>
                      cases assump_219
                      case intro assump_292 assump_293 =>
                        cases assump_292
                        case inl assump_294 =>
                          cases assump_293
                          case intro assump_298 assump_299 =>
                            cases assump_298
                            case intro assump_300 assump_301 =>
                              apply False.elim assump_301
                        case inr assump_295 =>
                          cases assump_293
                          case intro assump_308 assump_309 =>
                            cases assump_308
                            case intro assump_310 assump_311 =>
                              apply False.elim assump_311
      case inr assump_7 =>
        cases assump_3
        case intro assump_318 assump_319 =>
          cases assump_318
          case inl assump_320 =>
            cases assump_319
            case intro assump_324 assump_325 =>
              cases assump_324
              case inl assump_326 =>
                cases assump_325
                case intro assump_330 assump_331 =>
                  cases assump_330
                  case intro assump_332 assump_333 =>
                    apply False.elim assump_333
              case inr assump_327 =>
                cases assump_325
                case intro assump_340 assump_341 =>
                  cases assump_340
                  case intro assump_342 assump_343 =>
                    apply False.elim assump_343
          case inr assump_321 =>
            cases assump_321
            case intro assump_348 assump_349 =>
              cases assump_348
              case inl assump_350 =>
                cases assump_349
                case intro assump_354 assump_355 =>
                  cases assump_319
                  case intro assump_360 assump_361 =>
                    cases assump_360
                    case inl assump_362 =>
                      cases assump_361
                      case intro assump_366 assump_367 =>
                        cases assump_366
                        case intro assump_368 assump_369 =>
                          apply False.elim assump_369
                    case inr assump_363 =>
                      cases assump_361
                      case intro assump_376 assump_377 =>
                        cases assump_376
                        case intro assump_378 assump_379 =>
                          apply False.elim assump_379
              case inr assump_351 =>
                cases assump_349
                case intro assump_386 assump_387 =>
                  cases assump_319
                  case intro assump_392 assump_393 =>
                    cases assump_392
                    case inl assump_394 =>
                      cases assump_393
                      case intro assump_398 assump_399 =>
                        cases assump_398
                        case intro assump_400 assump_401 =>
                          apply False.elim assump_401
                    case inr assump_395 =>
                      cases assump_393
                      case intro assump_408 assump_409 =>
                        cases assump_408
                        case intro assump_410 assump_411 =>
                          apply False.elim assump_411
    case inr assump_5 =>
      cases assump_5
      case inl assump_416 =>
        cases assump_416
        case intro assump_418 assump_419 =>
          cases assump_419
          case inl assump_422 =>
            cases assump_3
            case intro assump_426 assump_427 =>
              cases assump_426
              case inl assump_428 =>
                cases assump_427
                case intro assump_432 assump_433 =>
                  cases assump_432
                  case inl assump_434 =>
                    cases assump_433
                    case intro assump_438 assump_439 =>
                      cases assump_438
                      case intro assump_440 assump_441 =>
                        apply False.elim assump_441
                  case inr assump_435 =>
                    cases assump_433
                    case intro assump_448 assump_449 =>
                      cases assump_448
                      case intro assump_450 assump_451 =>
                        apply False.elim assump_451
              case inr assump_429 =>
                cases assump_429
                case intro assump_456 assump_457 =>
                  cases assump_456
                  case inl assump_458 =>
                    cases assump_457
                    case intro assump_462 assump_463 =>
                      cases assump_427
                      case intro assump_468 assump_469 =>
                        cases assump_468
                        case inl assump_470 =>
                          cases assump_469
                          case intro assump_474 assump_475 =>
                            cases assump_474
                            case intro assump_476 assump_477 =>
                              apply False.elim assump_477
                        case inr assump_471 =>
                          cases assump_469
                          case intro assump_484 assump_485 =>
                            cases assump_484
                            case intro assump_486 assump_487 =>
                              apply False.elim assump_487
                  case inr assump_459 =>
                    cases assump_457
                    case intro assump_494 assump_495 =>
                      cases assump_427
                      case intro assump_500 assump_501 =>
                        cases assump_500
                        case inl assump_502 =>
                          cases assump_501
                          case intro assump_506 assump_507 =>
                            cases assump_506
                            case intro assump_508 assump_509 =>
                              apply False.elim assump_509
                        case inr assump_503 =>
                          cases assump_501
                          case intro assump_516 assump_517 =>
                            cases assump_516
                            case intro assump_518 assump_519 =>
                              apply False.elim assump_519
          case inr assump_423 =>
            cases assump_3
            case intro assump_526 assump_527 =>
              cases assump_526
              case inl assump_528 =>
                cases assump_527
                case intro assump_532 assump_533 =>
                  cases assump_532
                  case inl assump_534 =>
                    cases assump_533
                    case intro assump_538 assump_539 =>
                      cases assump_538
                      case intro assump_540 assump_541 =>
                        apply False.elim assump_541
                  case inr assump_535 =>
                    cases assump_533
                    case intro assump_548 assump_549 =>
                      cases assump_548
                      case intro assump_550 assump_551 =>
                        apply False.elim assump_551
              case inr assump_529 =>
                cases assump_529
                case intro assump_556 assump_557 =>
                  cases assump_556
                  case inl assump_558 =>
                    cases assump_557
                    case intro assump_562 assump_563 =>
                      cases assump_527
                      case intro assump_568 assump_569 =>
                        cases assump_568
                        case inl assump_570 =>
                          cases assump_569
                          case intro assump_574 assump_575 =>
                            cases assump_574
                            case intro assump_576 assump_577 =>
                              apply False.elim assump_577
                        case inr assump_571 =>
                          cases assump_569
                          case intro assump_584 assump_585 =>
                            cases assump_584
                            case intro assump_586 assump_587 =>
                              apply False.elim assump_587
                  case inr assump_559 =>
                    cases assump_557
                    case intro assump_594 assump_595 =>
                      cases assump_527
                      case intro assump_600 assump_601 =>
                        cases assump_600
                        case inl assump_602 =>
                          cases assump_601
                          case intro assump_606 assump_607 =>
                            cases assump_606
                            case intro assump_608 assump_609 =>
                              apply False.elim assump_609
                        case inr assump_603 =>
                          cases assump_601
                          case intro assump_616 assump_617 =>
                            cases assump_616
                            case intro assump_618 assump_619 =>
                              apply False.elim assump_619
      case inr assump_417 =>
        cases assump_417
        case intro assump_624 assump_625 =>
          cases assump_3
          case intro assump_630 assump_631 =>
            cases assump_630
            case inl assump_632 =>
              cases assump_631
              case intro assump_636 assump_637 =>
                cases assump_636
                case inl assump_638 =>
                  cases assump_637
                  case intro assump_642 assump_643 =>
                    cases assump_642
                    case intro assump_644 assump_645 =>
                      apply False.elim assump_645
                case inr assump_639 =>
                  cases assump_637
                  case intro assump_652 assump_653 =>
                    cases assump_652
                    case intro assump_654 assump_655 =>
                      apply False.elim assump_655
            case inr assump_633 =>
              cases assump_633
              case intro assump_660 assump_661 =>
                cases assump_660
                case inl assump_662 =>
                  cases assump_661
                  case intro assump_666 assump_667 =>
                    cases assump_631
                    case intro assump_672 assump_673 =>
                      cases assump_672
                      case inl assump_674 =>
                        cases assump_673
                        case intro assump_678 assump_679 =>
                          cases assump_678
                          case intro assump_680 assump_681 =>
                            apply False.elim assump_681
                      case inr assump_675 =>
                        cases assump_673
                        case intro assump_688 assump_689 =>
                          cases assump_688
                          case intro assump_690 assump_691 =>
                            apply False.elim assump_691
                case inr assump_663 =>
                  cases assump_661
                  case intro assump_698 assump_699 =>
                    cases assump_631
                    case intro assump_704 assump_705 =>
                      cases assump_704
                      case inl assump_706 =>
                        cases assump_705
                        case intro assump_710 assump_711 =>
                          cases assump_710
                          case intro assump_712 assump_713 =>
                            apply False.elim assump_713
                      case inr assump_707 =>
                        cases assump_705
                        case intro assump_720 assump_721 =>
                          cases assump_720
                          case intro assump_722 assump_723 =>
                            apply False.elim assump_723


variable (p4 p1 p6 p7 : Prop)
theorem file42_101025 : ((((((p7 ∧ False) ∨ (False → False)) ∨ ((p6 → False) ∧ (p4 ∨ p1))) → (((p1 → p1) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p7 ∧ False) ∨ (False → False)) ∨ ((p6 → False) ∧ (p4 ∨ p1))) → (((p1 → p1) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_12 =>
        have assump_61 : (p1 → p1) := by
          intro assump_23
          exact assump_23
        let assump_22 := assump_6 assump_61
        apply False.elim assump_22
    case inr assump_10 =>
      cases assump_10
      case intro assump_29 assump_30 =>
        cases assump_30
        case inl assump_33 =>
          have assump_62 : (p1 → p1) := by
            intro assump_40
            exact assump_40
          let assump_39 := assump_6 assump_62
          apply False.elim assump_39
        case inr assump_34 =>
          have assump_63 : (p1 → p1) := by
            intro assump_51
            exact assump_51
          let assump_50 := assump_6 assump_63
          apply False.elim assump_50
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p1 p6 p7 p5 p4 p3 : Prop)
theorem file42_102384 : ((((((p7 → False) ∧ (p5 → p6)) → ((True → False) → (p6 → p1))) ∨ (((p3 ∨ p7) → (p4 ∧ False)) ∨ ((p4 ∨ False) ∧ (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p7 → False) ∧ (p5 → p6)) → ((True → False) → (p6 → p1))) ∨ (((p3 ∨ p7) → (p4 ∧ False)) ∨ ((p4 ∨ False) ∧ (p7 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case intro assump_12 assump_13 =>
      have assump_28 : True := by
        apply True.intro
      let assump_20 := assump_6 assump_28
      apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p0 p2 p7 p3 p1 p5 p6 : Prop)
theorem file42_103095 : (((((p5 ∨ p0) ∨ (p0 ∧ p2)) → ((p3 ∧ False) → False)) → False) → ((((p6 ∧ p3) ∨ (p7 ∨ p2)) → ((p3 ∧ p5) → False)) → (((True → p0) ∨ (p1 → p2)) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  have assump_22 : (((p5 ∨ p0) ∨ (p0 ∧ p2)) → ((p3 ∧ False) → False)) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_10 := assump_1 assump_22
  apply False.elim assump_10


variable (p5 p0 : Prop)
theorem file42_103674 : (((((p5 ∧ p0) ∧ (False ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_21 : (((p5 ∧ p0) ∧ (False ∧ False)) → False) := by
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


variable (p7 p4 p6 p0 p3 p1 p2 : Prop)
theorem file42_104185 : (((((p6 → p2) ∨ (p1 → False)) → False) → (((p6 → True) ∨ (p2 → p1)) ∨ ((p4 → False) → (True ∧ p2)))) ∨ ((((p0 → p2) → (p0 ∧ False)) → False) → (((p0 → False) ∧ (p7 ∨ p2)) ∨ ((p3 → p3) ∨ (p2 ∨ p2))))) := by
  apply Or.inl
  intro assump_5
  apply Or.inl
  apply Or.inl
  intro assump_8
  apply True.intro


variable (p0 p5 p1 p2 : Prop)
theorem file42_104543 : (((((p5 ∨ p1) → (True ∨ p5)) ∨ ((p0 → True) ∨ (p2 → p5))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p5 ∨ p1) → (True ∨ p5)) ∨ ((p0 → True) ∨ (p2 → p5))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p7 p1 p0 p4 p5 p3 p2 : Prop)
theorem file42_105043 : (((((p6 ∨ p7) → (p2 → False)) ∨ ((p0 ∧ p0) → (p6 → False))) ∧ (((p5 → p4) ∨ (False ∧ p2)) ∧ ((p7 ∨ p4) → False))) → ((((False → False) → False) ∧ ((p2 ∧ p0) → (p1 → p1))) → (((p5 → False) ∨ (p5 → p3)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              have assump_130 : (False → False) := by
                intro assump_33
                apply False.elim assump_33
              let assump_32 := assump_8 assump_130
              apply False.elim assump_32
            case inr assump_23 =>
              cases assump_23
              case intro assump_39 assump_40 =>
                apply False.elim assump_39
        case inr assump_17 =>
          cases assump_15
          case intro assump_45 assump_46 =>
            cases assump_45
            case inl assump_47 =>
              have assump_131 : (False → False) := by
                intro assump_58
                apply False.elim assump_58
              let assump_57 := assump_8 assump_131
              apply False.elim assump_57
            case inr assump_48 =>
              cases assump_48
              case intro assump_64 assump_65 =>
                apply False.elim assump_64
  case inr assump_5 =>
    cases assump_2
    case intro assump_70 assump_71 =>
      cases assump_1
      case intro assump_76 assump_77 =>
        cases assump_76
        case inl assump_78 =>
          cases assump_77
          case intro assump_82 assump_83 =>
            cases assump_82
            case inl assump_84 =>
              have assump_132 : (False → False) := by
                intro assump_95
                apply False.elim assump_95
              let assump_94 := assump_70 assump_132
              apply False.elim assump_94
            case inr assump_85 =>
              cases assump_85
              case intro assump_101 assump_102 =>
                apply False.elim assump_101
        case inr assump_79 =>
          cases assump_77
          case intro assump_107 assump_108 =>
            cases assump_107
            case inl assump_109 =>
              have assump_133 : (False → False) := by
                intro assump_120
                apply False.elim assump_120
              let assump_119 := assump_70 assump_133
              apply False.elim assump_119
            case inr assump_110 =>
              cases assump_110
              case intro assump_126 assump_127 =>
                apply False.elim assump_126


variable (p0 p5 p2 p7 p1 p4 : Prop)
theorem file42_107887 : (((((p0 ∧ False) ∧ (True → False)) ∧ ((False ∧ p5) → False)) ∨ (((p2 ∨ p1) → (p7 ∨ p7)) ∧ ((p2 → p2) → False))) → ((((p0 → p4) ∧ (p4 → False)) → False) → False)) := by
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
          apply False.elim assump_12
  case inr assump_6 =>
    cases assump_6
    case intro assump_17 assump_18 =>
      have assump_30 : (p2 → p2) := by
        intro assump_24
        exact assump_24
      let assump_23 := assump_18 assump_30
      apply False.elim assump_23


variable (p6 p2 p7 p5 p1 p0 p4 : Prop)
theorem file42_108652 : (((((p6 ∨ False) ∧ (p6 → p2)) ∨ ((p7 ∧ p2) → False)) ∨ (((False → p4) → False) ∧ ((p4 ∧ p0) ∧ (p1 → p4)))) → ((((p6 → False) ∧ (p1 ∨ p4)) ∧ ((p2 → p1) ∧ (p5 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
      case inr assump_10 =>
        cases assump_4
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            apply False.elim assump_30


variable (p1 p5 p7 p0 p3 p6 p2 p4 : Prop)
theorem file42_109466 : (((((p4 → p1) ∨ (p5 ∨ p6)) ∨ ((p4 ∧ p5) ∧ (p2 ∧ p1))) → False) → ((((p0 → False) ∨ (False → False)) → ((p6 ∧ p7) ∨ (True → p1))) → (((p0 ∧ False) → (True → False)) ∨ ((p3 → True) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_7
  case intro assump_11 assump_12 =>
    apply False.elim assump_12


variable (p3 p1 p0 p6 p5 : Prop)
theorem file42_109887 : ((((((p5 ∧ False) → False) → ((p1 ∧ p6) → (False ∨ p3))) → (((p0 → False) ∧ (p0 ∨ False)) → False)) → False) → False) := by
  intro assump_9
  have assump_44 : ((((p5 ∧ False) → False) → ((p1 ∧ p6) → (False ∨ p3))) → (((p0 → False) ∧ (p0 ∨ False)) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_16
      case inl assump_19 =>
        have assump_45 : p0 := by
          exact assump_19
        let assump_35 := assump_15 assump_45
        apply False.elim assump_35
      case inr assump_20 =>
        apply False.elim assump_20
  let assump_12 := assump_9 assump_44
  apply False.elim assump_12


variable (p4 p2 p6 p1 p7 p0 p3 : Prop)
theorem file42_110632 : (((((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) → False) → ((((p0 ∧ p6) → (False ∧ p0)) ∨ ((False → p3) ∧ (p2 → p4))) ∧ (((p1 → False) ∧ (p4 → False)) ∧ ((p4 ∨ p7) → (p3 ∧ p1))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_183 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
      intro assump_14
      intro assump_15
      apply And.intro
      apply True.intro
      cases assump_14
      case intro assump_18 assump_19 =>
        have assump_184 : True := by
          apply True.intro
        let assump_26 := assump_15 assump_184
        apply False.elim assump_26
    let assump_13 := assump_1 assump_183
    apply False.elim assump_13
  cases assump_4
  case intro assump_33 assump_34 =>
    exact assump_33
  apply And.intro
  apply And.intro
  intro assump_39
  have assump_185 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
    intro assump_45
    intro assump_46
    apply And.intro
    apply True.intro
    cases assump_45
    case intro assump_49 assump_50 =>
      have assump_186 : True := by
        apply True.intro
      let assump_57 := assump_46 assump_186
      apply False.elim assump_57
  let assump_44 := assump_1 assump_185
  apply False.elim assump_44
  intro assump_64
  have assump_187 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
    intro assump_70
    intro assump_71
    apply And.intro
    apply True.intro
    cases assump_70
    case intro assump_74 assump_75 =>
      have assump_188 : p4 := by
        exact assump_64
      let assump_81 := assump_74 assump_188
      apply False.elim assump_81
  let assump_69 := assump_1 assump_187
  apply False.elim assump_69
  intro assump_88
  apply And.intro
  cases assump_88
  case inl assump_89 =>
    have assump_189 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
      intro assump_96
      intro assump_97
      apply And.intro
      apply True.intro
      cases assump_96
      case intro assump_100 assump_101 =>
        have assump_190 : p4 := by
          exact assump_89
        let assump_107 := assump_100 assump_190
        apply False.elim assump_107
    let assump_95 := assump_1 assump_189
    apply False.elim assump_95
  case inr assump_90 =>
    have assump_191 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
      intro assump_119
      intro assump_120
      apply And.intro
      apply True.intro
      cases assump_119
      case intro assump_123 assump_124 =>
        have assump_192 : p7 := by
          exact assump_90
        let assump_129 := assump_124 assump_192
        apply False.elim assump_129
    let assump_118 := assump_1 assump_191
    apply False.elim assump_118
  cases assump_88
  case inl assump_136 =>
    have assump_193 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
      intro assump_143
      intro assump_144
      apply And.intro
      apply True.intro
      cases assump_143
      case intro assump_147 assump_148 =>
        have assump_194 : p4 := by
          exact assump_136
        let assump_154 := assump_147 assump_194
        apply False.elim assump_154
    let assump_142 := assump_1 assump_193
    apply False.elim assump_142
  case inr assump_137 =>
    have assump_195 : (((p4 → False) ∧ (p7 → False)) → ((True → False) → (True ∧ p2))) := by
      intro assump_166
      intro assump_167
      apply And.intro
      apply True.intro
      cases assump_166
      case intro assump_170 assump_171 =>
        have assump_196 : p7 := by
          exact assump_137
        let assump_176 := assump_171 assump_196
        apply False.elim assump_176
    let assump_165 := assump_1 assump_195
    apply False.elim assump_165


variable (p2 p3 p4 p5 p7 p1 p0 : Prop)
theorem file42_114548 : (((((p7 ∧ False) → (False ∨ False)) ∧ ((p3 → False) → False)) ∧ (((p1 ∨ p4) ∨ (p1 → p2)) ∧ ((False → False) → False))) → ((((False → p2) → False) ∨ ((p1 → False) → False)) ∧ (((p4 → False) → (True ∨ p1)) ∨ ((p5 ∨ p4) → (p0 → p3))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            apply Or.inl
            intro assump_20
            have assump_96 : (False → False) := by
              intro assump_25
              apply False.elim assump_25
            let assump_24 := assump_11 assump_96
            apply False.elim assump_24
          case inr assump_15 =>
            apply Or.inl
            intro assump_35
            have assump_97 : (False → False) := by
              intro assump_40
              apply False.elim assump_40
            let assump_39 := assump_11 assump_97
            apply False.elim assump_39
        case inr assump_13 =>
          apply Or.inl
          intro assump_50
          have assump_98 : (False → False) := by
            intro assump_55
            apply False.elim assump_55
          let assump_54 := assump_11 assump_98
          apply False.elim assump_54
  cases assump_1
  case intro assump_61 assump_62 =>
    cases assump_61
    case intro assump_63 assump_64 =>
      cases assump_62
      case intro assump_69 assump_70 =>
        cases assump_69
        case inl assump_71 =>
          cases assump_71
          case inl assump_73 =>
            apply Or.inl
            intro assump_79
            apply Or.inl
            apply True.intro
          case inr assump_74 =>
            apply Or.inl
            intro assump_86
            apply Or.inl
            apply True.intro
        case inr assump_72 =>
          apply Or.inl
          intro assump_93
          apply Or.inl
          apply True.intro


variable (p6 p2 p7 p0 p1 p4 p3 : Prop)
theorem file42_116661 : (((((False → False) ∧ (p7 → False)) ∧ ((p6 ∨ p2) ∨ (p3 ∨ p4))) → (((p2 → False) ∧ (False ∨ False)) → ((p2 → False) → False))) ∨ ((((False → False) ∨ (p1 → p3)) ∧ ((p3 ∨ p3) → False)) → (((p4 ∧ p4) → False) → ((p2 → p0) ∧ (p7 ∨ p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      apply False.elim assump_11


variable (p0 p6 p2 p7 p3 p4 p5 : Prop)
theorem file42_117219 : ((((((p0 ∧ p3) → (p4 ∨ True)) ∨ ((True ∨ p5) ∨ (p7 ∧ p4))) ∧ (((p3 → False) → False) ∧ ((False ∧ p2) ∧ (p6 ∨ p0)))) ∧ ((((p2 → False) → (p0 ∧ p3)) ∧ ((False ∧ p6) ∨ (False → p2))) ∨ (((p4 → False) → False) ∧ ((p5 → False) ∨ (True ∨ p2))))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            cases assump_5
            case intro assump_26 assump_27 =>
              cases assump_27
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
          case inr assump_23 =>
            cases assump_5
            case intro assump_38 assump_39 =>
              cases assump_39
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  apply False.elim assump_44
        case inr assump_21 =>
          cases assump_21
          case intro assump_48 assump_49 =>
            cases assump_5
            case intro assump_54 assump_55 =>
              cases assump_55
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  apply False.elim assump_60


variable (p0 p7 p1 p2 : Prop)
theorem file42_119053 : (((((p2 → True) ∧ (p0 → p0)) ∨ ((p1 → False) ∧ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p2 → True) ∧ (p0 → p0)) ∨ ((p1 → False) ∧ (p7 → False))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply True.intro
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p6 p7 p1 p3 p2 p0 : Prop)
theorem file42_119484 : (((((p0 → True) ∨ (False → p0)) → False) → False) → ((((p6 ∨ p5) ∨ (p5 → p7)) ∧ ((p0 → False) → (p6 → False))) → (((True ∨ p2) ∨ (p3 ∧ p1)) ∨ ((p3 → False) ∨ (p3 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_8 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p3 p4 p6 p7 p0 p5 p1 p2 : Prop)
theorem file42_120213 : (((((p7 → False) ∨ (p7 ∨ False)) ∨ ((p4 → False) → False)) → (((p3 ∨ p4) ∨ (p6 → p1)) ∧ ((p2 → False) ∨ (p0 ∨ p3)))) → ((((False ∨ p1) → (p5 → p5)) → ((p3 ∧ False) → (p4 ∨ p0))) ∨ (((p7 ∨ p6) → (p5 ∨ p7)) ∨ ((p7 ∧ True) → (False ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p4 p5 p1 p3 : Prop)
theorem file42_120659 : (((((False ∧ p1) ∧ (p4 → False)) → ((p3 → p5) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : (((False ∧ p1) ∧ (p4 → False)) → ((p3 → p5) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p0 p1 p3 : Prop)
theorem file42_121144 : ((((((p6 → True) → False) → False) ∨ (((p0 ∨ True) → (p1 ∨ p1)) → ((p6 ∨ p3) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p6 → True) → False) → False) ∨ (((p0 ∨ True) → (p1 ∨ p1)) → ((p6 ∨ p3) ∨ (p0 → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_17 : (p6 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p0 p7 p1 p3 : Prop)
theorem file42_121708 : ((((((True ∨ p1) → (p6 → True)) → False) → (((p0 ∨ p3) ∨ (p6 → False)) ∨ ((p6 → False) ∧ (p7 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True ∨ p1) → (p6 → True)) → False) → (((p0 ∨ p3) ∨ (p6 → False)) ∨ ((p6 → False) ∧ (p7 ∧ p6)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_22 : ((True ∨ p1) → (p6 → True)) := by
      intro assump_13
      intro assump_14
      apply True.intro
    let assump_12 := assump_5 assump_22
    apply False.elim assump_12
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p7 p0 p5 p2 : Prop)
theorem file42_122363 : ((((((p0 ∨ p2) ∧ (p1 → False)) ∧ ((p5 ∨ p5) ∨ (p7 → False))) → (((True ∨ p2) → False) → ((p7 → False) → (p0 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_129 : ((((p0 ∨ p2) ∧ (p1 → False)) ∧ ((p5 ∨ p5) ∨ (p7 → False))) → (((True ∨ p2) → False) → ((p7 → False) → (p0 ∧ p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_5
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_13
          case inl assump_22 =>
            cases assump_22
            case inl assump_24 =>
              exact assump_16
            case inr assump_25 =>
              exact assump_16
          case inr assump_23 =>
            exact assump_16
        case inr assump_17 =>
          cases assump_13
          case inl assump_36 =>
            cases assump_36
            case inl assump_38 =>
              have assump_130 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_45 := assump_6 assump_130
              apply False.elim assump_45
            case inr assump_39 =>
              have assump_131 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_54 := assump_6 assump_131
              apply False.elim assump_54
          case inr assump_37 =>
            have assump_132 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_63 := assump_6 assump_132
            apply False.elim assump_63
    cases assump_5
    case intro assump_71 assump_72 =>
      cases assump_71
      case intro assump_73 assump_74 =>
        cases assump_73
        case inl assump_75 =>
          cases assump_72
          case inl assump_81 =>
            cases assump_81
            case inl assump_83 =>
              exact assump_75
            case inr assump_84 =>
              exact assump_75
          case inr assump_82 =>
            exact assump_75
        case inr assump_76 =>
          cases assump_72
          case inl assump_95 =>
            cases assump_95
            case inl assump_97 =>
              have assump_133 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_104 := assump_6 assump_133
              apply False.elim assump_104
            case inr assump_98 =>
              have assump_134 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_113 := assump_6 assump_134
              apply False.elim assump_113
          case inr assump_96 =>
            have assump_135 : (True ∨ p2) := by
              apply Or.inl
              apply True.intro
            let assump_122 := assump_6 assump_135
            apply False.elim assump_122
  let assump_4 := assump_1 assump_129
  apply False.elim assump_4


variable (p0 p4 p2 p5 : Prop)
theorem file42_125395 : (((((p2 → True) ∨ (False ∧ True)) → False) → False) ∨ ((((p0 → p2) ∨ (p5 ∧ p2)) → ((p2 → False) → False)) ∨ (((p4 → True) → (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p2 → True) ∨ (False ∧ True)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p2 p0 p3 p7 p6 p5 p4 : Prop)
theorem file42_125821 : ((((((p2 ∧ p0) → False) ∧ ((p7 ∧ p2) → False)) ∨ (((p4 → False) ∨ (False → p0)) ∧ ((p4 ∨ False) ∧ (p6 ∧ p5)))) ∧ ((((True → False) ∨ (p7 ∧ p0)) → ((p0 → p6) → (p0 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_120 : (((True → False) ∨ (p7 ∧ p0)) → ((p0 → p6) → (p0 ∨ p3))) := by
          intro assump_15
          intro assump_16
          cases assump_15
          case inl assump_19 =>
            have assump_121 : True := by
              apply True.intro
            let assump_23 := assump_19 assump_121
            apply False.elim assump_23
          case inr assump_20 =>
            cases assump_20
            case intro assump_27 assump_28 =>
              apply Or.inl
              exact assump_28
        let assump_14 := assump_3 assump_120
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_36
        case inl assump_38 =>
          cases assump_37
          case intro assump_42 assump_43 =>
            cases assump_42
            case inl assump_44 =>
              cases assump_43
              case intro assump_48 assump_49 =>
                have assump_122 : (((True → False) ∨ (p7 ∧ p0)) → ((p0 → p6) → (p0 ∨ p3))) := by
                  intro assump_57
                  intro assump_58
                  cases assump_57
                  case inl assump_61 =>
                    have assump_123 : True := by
                      apply True.intro
                    let assump_65 := assump_61 assump_123
                    apply False.elim assump_65
                  case inr assump_62 =>
                    cases assump_62
                    case intro assump_69 assump_70 =>
                      apply Or.inl
                      exact assump_70
                let assump_56 := assump_3 assump_122
                apply False.elim assump_56
            case inr assump_45 =>
              apply False.elim assump_45
        case inr assump_39 =>
          cases assump_37
          case intro assump_82 assump_83 =>
            cases assump_82
            case inl assump_84 =>
              cases assump_83
              case intro assump_88 assump_89 =>
                have assump_124 : (((True → False) ∨ (p7 ∧ p0)) → ((p0 → p6) → (p0 ∨ p3))) := by
                  intro assump_97
                  intro assump_98
                  cases assump_97
                  case inl assump_101 =>
                    have assump_125 : True := by
                      apply True.intro
                    let assump_105 := assump_101 assump_125
                    apply False.elim assump_105
                  case inr assump_102 =>
                    cases assump_102
                    case intro assump_109 assump_110 =>
                      apply Or.inl
                      exact assump_110
                let assump_96 := assump_3 assump_124
                apply False.elim assump_96
            case inr assump_85 =>
              apply False.elim assump_85


variable (p1 p6 p0 p4 p7 : Prop)
theorem file42_129059 : ((((((p0 → p4) → (p7 ∨ p4)) → False) → False) ∧ ((((False ∨ False) ∧ (p6 ∨ p1)) → ((p7 → False) ∨ (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((False ∨ False) ∧ (p6 ∨ p1)) → ((p7 → False) ∨ (p7 → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p2 p1 p6 p4 p0 p5 p7 : Prop)
theorem file42_129728 : ((((((p0 → False) ∨ (p4 → False)) ∧ ((p2 ∨ p6) ∧ (p6 → False))) → (((p6 ∧ True) ∨ (True ∧ p1)) → ((False ∧ p7) ∨ (p5 → p5)))) ∧ ((((p1 ∨ True) → False) → ((False → False) ∧ (p5 ∧ p0))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_32 : (((p1 ∨ True) → False) → ((False → False) ∧ (p5 ∧ p0))) := by
      intro assump_13
      apply And.intro
      intro assump_14
      apply False.elim assump_14
      apply And.intro
      have assump_33 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_19 := assump_13 assump_33
      apply False.elim assump_19
      have assump_34 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_25 := assump_13 assump_34
      apply False.elim assump_25
    let assump_12 := assump_7 assump_32
    apply False.elim assump_12


variable (p5 p4 : Prop)
theorem file42_130655 : ((((((True → False) → (p4 → p5)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p4 → p5)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True → False) → (p4 → p5)) := by
      intro assump_9
      intro assump_10
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p4 p3 p7 p5 p1 p6 : Prop)
theorem file42_131270 : (((((p7 → p6) ∨ (p6 → False)) ∨ ((p6 ∨ p5) → (p1 ∨ p0))) → (((p0 ∨ p0) → (p0 ∧ p3)) ∨ ((p0 → False) ∧ (p7 ∧ p3)))) → ((((False → p0) → False) → False) → (((p4 ∨ p4) → (p4 ∨ p5)) ∨ ((p0 ∨ False) ∧ (True → p3))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    apply Or.inl
    exact assump_8
  case inr assump_9 =>
    apply Or.inl
    exact assump_9


variable (p5 p7 p1 p0 p6 p3 p2 p4 : Prop)
theorem file42_131755 : (((((p3 ∧ p6) ∨ (p5 ∧ p4)) → ((p5 → False) ∨ (p0 ∨ p4))) → False) → ((((False → False) ∧ (False → p1)) → False) → (((p4 ∧ p7) ∧ (p2 ∨ p3)) ∨ ((p6 → p6) ∨ (p6 ∧ p5))))) := by
  intro assump_9
  intro assump_10
  apply Or.inr
  apply Or.inl
  intro assump_15
  exact assump_15


variable (p2 p0 p1 p5 p4 p7 p3 : Prop)
theorem file42_132093 : ((((((p3 ∨ p5) → (p5 → False)) ∧ ((p0 → p1) → (p2 → False))) → (((True → False) ∧ (p4 → p7)) → ((p4 ∨ True) ∨ (p4 ∨ False)))) → False) → False) := by
  intro assump_5
  have assump_26 : ((((p3 ∨ p5) → (p5 → False)) ∧ ((p0 → p1) → (p2 → False))) → (((True → False) ∧ (p4 → p7)) → ((p4 ∨ True) ∨ (p4 ∨ False)))) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_9
      case intro assump_17 assump_18 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_8 := assump_5 assump_26
  apply False.elim assump_8


