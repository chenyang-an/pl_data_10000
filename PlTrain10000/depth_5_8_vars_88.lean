variable (p6 p3 p5 p2 p0 p4 p7 : Prop)
theorem file88_47 : (((((True → p7) ∨ (p4 → p3)) ∨ ((p4 ∧ p2) ∧ (True → False))) ∧ (((p2 ∧ False) → False) → False)) → ((((p3 → False) ∧ (False → p5)) → ((p6 ∧ p0) ∧ (False ∧ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_64 : ((p2 ∧ False) → False) := by
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
        let assump_15 := assump_6 assump_64
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_65 : ((p2 ∧ False) → False) := by
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            apply False.elim assump_33
        let assump_30 := assump_6 assump_65
        apply False.elim assump_30
    case inr assump_8 =>
      cases assump_8
      case intro assump_41 assump_42 =>
        cases assump_41
        case intro assump_43 assump_44 =>
          have assump_66 : ((p2 ∧ False) → False) := by
            intro assump_54
            cases assump_54
            case intro assump_55 assump_56 =>
              apply False.elim assump_56
          let assump_53 := assump_6 assump_66
          apply False.elim assump_53


variable (p4 p5 p7 p1 p6 p3 p2 : Prop)
theorem file88_1462 : (((((p4 → p1) → (p7 → p1)) ∨ ((p2 ∧ False) ∨ (p3 → False))) ∧ (((True → False) ∧ (p4 → False)) ∧ ((False → False) → False))) → ((((p5 ∧ p1) ∨ (p2 ∨ p3)) → ((p1 → False) ∧ (True ∨ p5))) ∨ (((p1 → p3) → (p3 ∨ p4)) ∧ ((p6 ∨ p7) ∨ (p3 → p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_18
          apply And.intro
          intro assump_19
          cases assump_18
          case inl assump_22 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              have assump_158 : (False → False) := by
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_9 assump_158
              apply False.elim assump_33
          case inr assump_23 =>
            cases assump_23
            case inl assump_40 =>
              have assump_159 : (False → False) := by
                intro assump_47
                apply False.elim assump_47
              let assump_46 := assump_9 assump_159
              apply False.elim assump_46
            case inr assump_41 =>
              have assump_160 : (False → False) := by
                intro assump_58
                apply False.elim assump_58
              let assump_57 := assump_9 assump_160
              apply False.elim assump_57
          cases assump_18
          case inl assump_64 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              apply Or.inl
              apply True.intro
          case inr assump_65 =>
            cases assump_65
            case inl assump_72 =>
              apply Or.inl
              apply True.intro
            case inr assump_73 =>
              apply Or.inl
              apply True.intro
    case inr assump_5 =>
      cases assump_5
      case inl assump_78 =>
        cases assump_78
        case intro assump_80 assump_81 =>
          apply False.elim assump_81
      case inr assump_79 =>
        cases assump_3
        case intro assump_88 assump_89 =>
          cases assump_88
          case intro assump_90 assump_91 =>
            apply Or.inl
            intro assump_98
            apply And.intro
            intro assump_99
            cases assump_98
            case inl assump_102 =>
              cases assump_102
              case intro assump_104 assump_105 =>
                have assump_161 : (False → False) := by
                  intro assump_114
                  apply False.elim assump_114
                let assump_113 := assump_89 assump_161
                apply False.elim assump_113
            case inr assump_103 =>
              cases assump_103
              case inl assump_120 =>
                have assump_162 : (False → False) := by
                  intro assump_127
                  apply False.elim assump_127
                let assump_126 := assump_89 assump_162
                apply False.elim assump_126
              case inr assump_121 =>
                have assump_163 : (False → False) := by
                  intro assump_138
                  apply False.elim assump_138
                let assump_137 := assump_89 assump_163
                apply False.elim assump_137
            cases assump_98
            case inl assump_144 =>
              cases assump_144
              case intro assump_146 assump_147 =>
                apply Or.inl
                apply True.intro
            case inr assump_145 =>
              cases assump_145
              case inl assump_152 =>
                apply Or.inl
                apply True.intro
              case inr assump_153 =>
                apply Or.inl
                apply True.intro


variable (p5 p6 p1 p7 p0 p3 : Prop)
theorem file88_5374 : ((((((p1 ∧ p0) → (p5 → False)) ∧ ((p7 ∨ p0) → False)) → False) ∧ ((((p5 → p3) → False) ∧ ((p3 → p6) → (p6 → False))) ∧ (((False → False) ∨ (False ∧ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_23 : ((False → False) ∨ (False ∧ p6)) := by
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_7 assump_23
        apply False.elim assump_16


variable (p4 p6 p0 p5 p2 p3 : Prop)
theorem file88_6024 : (((((p6 ∨ p2) → False) → False) → (((True → False) ∨ (True → False)) → ((p0 → p4) ∧ (p6 → False)))) → ((((False ∧ p4) ∧ (p2 ∧ p3)) ∧ ((p4 ∨ p5) ∨ (True ∧ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p3 p4 p6 p7 p1 p5 p2 p0 : Prop)
theorem file88_6499 : (((((p1 ∨ p7) ∨ (p1 → False)) ∧ ((True ∨ p3) → False)) → (((p2 → p6) → (p6 → False)) ∧ ((False ∧ p2) ∧ (p5 → p4)))) → ((((p7 ∨ p1) ∧ (p7 ∧ False)) ∧ ((p2 ∧ p4) → (p7 → p4))) ∨ (((False → False) ∧ (p1 ∧ p0)) ∨ ((p6 → p6) ∨ (p6 ∨ False))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inr
  apply Or.inl
  intro assump_7
  exact assump_7


variable (p6 p1 p0 p2 p5 p7 p4 p3 : Prop)
theorem file88_6906 : ((((((p1 ∧ p3) ∧ (p5 ∧ p4)) ∨ ((p7 → p6) → (False → False))) ∨ (((p6 → False) → (p2 → False)) → ((p0 ∧ p0) ∨ (True → p0)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p1 ∧ p3) ∧ (p5 ∧ p4)) ∨ ((p7 → p6) → (False → False))) ∨ (((p6 → False) → (p2 → False)) → ((p0 ∧ p0) ∨ (True → p0)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p5 p1 p6 p3 p0 p2 p4 : Prop)
theorem file88_7451 : (((((False → False) → False) ∧ ((p4 ∨ p5) ∧ (p6 ∨ p6))) → (((p4 → False) ∧ (p2 ∨ p6)) → ((p2 → False) → (p5 → False)))) ∨ ((((p5 ∨ p4) ∨ (p2 → True)) ∨ ((p3 ∨ p1) → (p2 → False))) ∨ (((p0 → p0) ∨ (p7 ∨ True)) ∧ ((p3 → p7) ∧ (p3 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case inl assump_13 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_22
            case inl assump_27 =>
              have assump_139 : (False → False) := by
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_17 assump_139
              apply False.elim assump_33
            case inr assump_28 =>
              have assump_140 : (False → False) := by
                intro assump_45
                apply False.elim assump_45
              let assump_44 := assump_17 assump_140
              apply False.elim assump_44
          case inr assump_24 =>
            cases assump_22
            case inl assump_53 =>
              have assump_141 : (False → False) := by
                intro assump_60
                apply False.elim assump_60
              let assump_59 := assump_17 assump_141
              apply False.elim assump_59
            case inr assump_54 =>
              have assump_142 : (False → False) := by
                intro assump_71
                apply False.elim assump_71
              let assump_70 := assump_17 assump_142
              apply False.elim assump_70
    case inr assump_14 =>
      cases assump_1
      case intro assump_79 assump_80 =>
        cases assump_80
        case intro assump_83 assump_84 =>
          cases assump_83
          case inl assump_85 =>
            cases assump_84
            case inl assump_89 =>
              have assump_143 : (False → False) := by
                intro assump_96
                apply False.elim assump_96
              let assump_95 := assump_79 assump_143
              apply False.elim assump_95
            case inr assump_90 =>
              have assump_144 : (False → False) := by
                intro assump_107
                apply False.elim assump_107
              let assump_106 := assump_79 assump_144
              apply False.elim assump_106
          case inr assump_86 =>
            cases assump_84
            case inl assump_115 =>
              have assump_145 : (False → False) := by
                intro assump_122
                apply False.elim assump_122
              let assump_121 := assump_79 assump_145
              apply False.elim assump_121
            case inr assump_116 =>
              have assump_146 : (False → False) := by
                intro assump_133
                apply False.elim assump_133
              let assump_132 := assump_79 assump_146
              apply False.elim assump_132


variable (p1 p2 p0 p5 p7 p4 p6 p3 : Prop)
theorem file88_10576 : (((((p3 → False) → (p0 ∧ True)) ∧ ((p3 → False) → False)) ∧ (((p1 ∨ p1) ∨ (p4 ∨ p3)) → False)) → ((((p3 ∧ p4) → (p2 ∨ p4)) → ((p1 ∨ p6) ∨ (p2 ∧ p0))) ∨ (((p3 → False) → (p7 ∨ p5)) ∧ ((p5 → False) ∧ (p3 → p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      have assump_30 : (p3 → False) := by
        intro assump_18
        have assump_31 : ((p1 ∨ p1) ∨ (p4 ∨ p3)) := by
          apply Or.inr
          apply Or.inr
          exact assump_18
        let assump_23 := assump_3 assump_31
        apply False.elim assump_23
      let assump_17 := assump_5 assump_30
      apply False.elim assump_17


variable (p0 p6 p3 p4 p1 : Prop)
theorem file88_11362 : ((((((p6 → False) ∨ (True ∨ p4)) ∧ ((True → False) ∧ (p1 → False))) → (((p1 → p1) → False) → ((True → False) → (p3 → p0)))) → False) → False) := by
  intro assump_1
  have assump_63 : ((((p6 → False) ∨ (True ∨ p4)) ∧ ((True → False) ∧ (p1 → False))) → (((p1 → p1) → False) → ((True → False) → (p3 → p0)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_16
        case intro assump_21 assump_22 =>
          have assump_64 : True := by
            apply True.intro
          let assump_28 := assump_21 assump_64
          apply False.elim assump_28
      case inr assump_18 =>
        cases assump_18
        case inl assump_32 =>
          cases assump_16
          case intro assump_36 assump_37 =>
            have assump_65 : True := by
              apply True.intro
            let assump_43 := assump_36 assump_65
            apply False.elim assump_43
        case inr assump_33 =>
          cases assump_16
          case intro assump_49 assump_50 =>
            have assump_66 : True := by
              apply True.intro
            let assump_56 := assump_49 assump_66
            apply False.elim assump_56
  let assump_4 := assump_1 assump_63
  apply False.elim assump_4


variable (p4 p0 p6 p7 p2 p5 : Prop)
theorem file88_12769 : ((((((False ∨ True) → (p6 → False)) ∧ ((True ∧ p2) ∧ (p7 → False))) → (((p0 → False) ∧ (p5 ∧ p4)) → ((p5 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((False ∨ True) → (p6 → False)) ∧ ((True ∧ p2) ∧ (p7 → False))) → (((p0 → False) ∧ (p5 ∧ p4)) → ((p5 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p7 p3 p0 p6 p2 p5 : Prop)
theorem file88_13355 : (((((p7 ∧ p7) ∧ (p7 → False)) → ((p0 ∧ p2) → (p6 → False))) ∨ (((p0 ∧ True) → (p5 ∨ True)) → ((p2 → False) ∧ (p2 → False)))) ∨ ((((False ∨ p5) ∧ (p4 → p0)) ∨ ((p0 ∧ p3) → (p3 ∨ p0))) → (((False ∨ p6) → False) → ((p6 → False) ∧ (p5 ∧ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_50
  intro assump_51
  intro assump_52
  cases assump_51
  case intro assump_55 assump_56 =>
    cases assump_50
    case intro assump_61 assump_62 =>
      cases assump_61
      case intro assump_63 assump_64 =>
        have assump_75 : p7 := by
          exact assump_64
        let assump_71 := assump_62 assump_75
        apply False.elim assump_71


variable (p5 p6 p4 p7 p3 : Prop)
theorem file88_14060 : (((((p3 ∨ True) ∧ (p7 ∧ p4)) → False) ∧ (((p4 → False) ∧ (False ∨ False)) ∧ ((False ∧ p4) ∧ (p5 ∧ False)))) → ((((False ∧ p3) ∨ (p4 → p4)) → ((p3 → False) ∨ (p6 → False))) → False)) := by
  intro assump_24
  intro assump_25
  cases assump_24
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_35
        case inl assump_38 =>
          apply False.elim assump_38
        case inr assump_39 =>
          apply False.elim assump_39


variable (p0 p6 p4 p5 p1 p7 : Prop)
theorem file88_14676 : (((((p6 ∨ p6) ∨ (p5 → p5)) → False) → False) ∨ ((((p5 → False) ∨ (p5 ∨ p6)) → False) → (((p0 ∧ p7) ∨ (p1 → False)) ∧ ((True ∨ p4) ∧ (True → False))))) := by
  apply Or.inl
  intro assump_18
  have assump_28 : ((p6 ∨ p6) ∨ (p5 → p5)) := by
    apply Or.inr
    intro assump_22
    exact assump_22
  let assump_21 := assump_18 assump_28
  apply False.elim assump_21


variable (p1 p5 p6 p3 p4 : Prop)
theorem file88_15097 : ((((((True → False) → False) → ((p5 ∧ p3) → (p3 → p4))) ∧ (((p1 → p6) → False) → ((p1 ∧ False) → False))) ∧ ((((p4 → False) ∧ (p6 ∧ p6)) → ((p4 ∨ True) ∨ (False ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_27 : (((p4 → False) ∧ (p6 ∧ p6)) → ((p4 ∨ True) ∨ (False ∨ p1))) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply Or.inl
            apply Or.inr
            apply True.intro
      let assump_12 := assump_3 assump_27
      apply False.elim assump_12


variable (p0 p3 p4 p2 : Prop)
theorem file88_15871 : (((((p3 → p4) ∨ (p2 ∧ p3)) ∧ ((p4 → False) ∧ (p3 ∧ p0))) ∧ (((p0 ∨ False) ∧ (False → p4)) → False)) → False) := by
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
            have assump_54 : ((p0 ∨ False) ∧ (False → p4)) := by
              apply And.intro
              apply Or.inl
              exact assump_15
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_3 assump_54
            apply False.elim assump_22
      case inr assump_7 =>
        cases assump_7
        case intro assump_29 assump_30 =>
          cases assump_5
          case intro assump_35 assump_36 =>
            cases assump_36
            case intro assump_39 assump_40 =>
              have assump_55 : ((p0 ∨ False) ∧ (False → p4)) := by
                apply And.intro
                apply Or.inl
                exact assump_40
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_3 assump_55
              apply False.elim assump_47


variable (p2 p0 p5 p4 p7 : Prop)
theorem file88_17220 : (((((p4 ∨ p2) ∧ (p2 ∨ p4)) → ((p0 → False) → (p5 ∧ p4))) ∨ (((False → False) → False) ∨ ((False → False) → False))) → ((((False → False) → False) → ((p5 ∧ p7) → False)) ∨ (((p2 → False) ∧ (True → False)) ∨ ((p7 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      have assump_63 : (False → False) := by
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_6 assump_63
      apply False.elim assump_16
  case inr assump_3 =>
    cases assump_3
    case inl assump_23 =>
      apply Or.inl
      intro assump_27
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        have assump_64 : (False → False) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_27 assump_64
        apply False.elim assump_37
    case inr assump_24 =>
      apply Or.inl
      intro assump_46
      intro assump_47
      cases assump_47
      case intro assump_48 assump_49 =>
        have assump_65 : (False → False) := by
          intro assump_57
          apply False.elim assump_57
        let assump_56 := assump_46 assump_65
        apply False.elim assump_56


variable (p2 p1 p4 p6 p3 : Prop)
theorem file88_18585 : ((((((False → False) ∨ (True → False)) → ((p4 → p3) ∨ (p6 → False))) → (((p2 ∧ p1) → (p3 ∨ True)) ∨ ((True → False) → False))) → False) → False) := by
  intro assump_41
  have assump_58 : ((((False → False) ∨ (True → False)) → ((p4 → p3) ∨ (p6 → False))) → (((p2 ∧ p1) → (p3 ∨ True)) ∨ ((True → False) → False))) := by
    intro assump_45
    apply Or.inl
    intro assump_48
    cases assump_48
    case intro assump_49 assump_50 =>
      apply Or.inr
      apply True.intro
  let assump_44 := assump_41 assump_58
  apply False.elim assump_44


variable (p4 p7 p5 p3 : Prop)
theorem file88_19183 : ((((((p3 ∨ True) ∨ (p7 → False)) ∨ ((p5 → False) → (p3 ∨ p3))) → (((False → True) ∧ (p7 ∨ p4)) ∨ ((p5 → False) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p3 ∨ True) ∨ (p7 → False)) ∨ ((p5 → False) → (p3 ∨ p3))) → (((False → True) ∧ (p7 ∨ p4)) ∨ ((p5 → False) → (False → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inr
          intro assump_15
          intro assump_16
          apply False.elim assump_16
        case inr assump_11 =>
          apply Or.inr
          intro assump_22
          intro assump_23
          apply False.elim assump_23
      case inr assump_9 =>
        apply Or.inr
        intro assump_29
        intro assump_30
        apply False.elim assump_30
    case inr assump_7 =>
      apply Or.inr
      intro assump_36
      intro assump_37
      apply False.elim assump_37
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p2 p5 p4 p0 p7 : Prop)
theorem file88_20303 : ((((((p2 ∧ p0) → (True → False)) → ((p4 → True) → False)) → (((False → p5) → (False → False)) ∨ ((p7 ∨ p2) ∧ (p5 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∧ p0) → (True → False)) → ((p4 → True) → False)) → (((False → p5) → (False → False)) ∨ ((p7 ∨ p2) ∧ (p5 ∧ False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p5 p3 p1 p0 p6 : Prop)
theorem file88_20846 : (((((p5 ∨ p2) ∨ (p3 ∨ p6)) ∨ ((p5 → False) → (p2 → p2))) ∧ (((True ∨ p1) → (p1 ∧ False)) → False)) ∨ ((((p1 → False) ∨ (p1 ∧ p5)) ∨ ((p0 → p5) ∧ (False → False))) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_7
  intro assump_8
  exact assump_8
  intro assump_13
  have assump_22 : (True ∨ p1) := by
    apply Or.inl
    apply True.intro
  let assump_16 := assump_13 assump_22
  let assump_17 := And.right assump_16
  apply False.elim assump_17


variable (p3 p1 p4 p0 p7 p2 : Prop)
theorem file88_21384 : ((((((True ∨ p2) → (True → False)) ∨ ((p0 ∨ p2) → (p4 ∧ False))) ∨ (((p1 ∧ False) → False) → False)) ∧ ((((p0 → p3) ∧ (p7 ∨ p1)) ∧ ((p3 → False) ∧ (True → False))) ∧ (((p2 ∨ p4) ∧ (p4 ∧ p2)) ∧ ((p4 ∧ False) ∧ (False → False))))) → False) := by
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_22
              case inl assump_25 =>
                cases assump_20
                case intro assump_29 assump_30 =>
                  cases assump_18
                  case intro assump_35 assump_36 =>
                    cases assump_35
                    case intro assump_37 assump_38 =>
                      cases assump_37
                      case inl assump_39 =>
                        cases assump_38
                        case intro assump_43 assump_44 =>
                          cases assump_36
                          case intro assump_49 assump_50 =>
                            cases assump_49
                            case intro assump_51 assump_52 =>
                              apply False.elim assump_52
                      case inr assump_40 =>
                        cases assump_38
                        case intro assump_59 assump_60 =>
                          cases assump_36
                          case intro assump_65 assump_66 =>
                            cases assump_65
                            case intro assump_67 assump_68 =>
                              apply False.elim assump_68
              case inr assump_26 =>
                cases assump_20
                case intro assump_75 assump_76 =>
                  cases assump_18
                  case intro assump_81 assump_82 =>
                    cases assump_81
                    case intro assump_83 assump_84 =>
                      cases assump_83
                      case inl assump_85 =>
                        cases assump_84
                        case intro assump_89 assump_90 =>
                          cases assump_82
                          case intro assump_95 assump_96 =>
                            cases assump_95
                            case intro assump_97 assump_98 =>
                              apply False.elim assump_98
                      case inr assump_86 =>
                        cases assump_84
                        case intro assump_105 assump_106 =>
                          cases assump_82
                          case intro assump_111 assump_112 =>
                            cases assump_111
                            case intro assump_113 assump_114 =>
                              apply False.elim assump_114
      case inr assump_14 =>
        cases assump_10
        case intro assump_121 assump_122 =>
          cases assump_121
          case intro assump_123 assump_124 =>
            cases assump_123
            case intro assump_125 assump_126 =>
              cases assump_126
              case inl assump_129 =>
                cases assump_124
                case intro assump_133 assump_134 =>
                  cases assump_122
                  case intro assump_139 assump_140 =>
                    cases assump_139
                    case intro assump_141 assump_142 =>
                      cases assump_141
                      case inl assump_143 =>
                        cases assump_142
                        case intro assump_147 assump_148 =>
                          cases assump_140
                          case intro assump_153 assump_154 =>
                            cases assump_153
                            case intro assump_155 assump_156 =>
                              apply False.elim assump_156
                      case inr assump_144 =>
                        cases assump_142
                        case intro assump_163 assump_164 =>
                          cases assump_140
                          case intro assump_169 assump_170 =>
                            cases assump_169
                            case intro assump_171 assump_172 =>
                              apply False.elim assump_172
              case inr assump_130 =>
                cases assump_124
                case intro assump_179 assump_180 =>
                  cases assump_122
                  case intro assump_185 assump_186 =>
                    cases assump_185
                    case intro assump_187 assump_188 =>
                      cases assump_187
                      case inl assump_189 =>
                        cases assump_188
                        case intro assump_193 assump_194 =>
                          cases assump_186
                          case intro assump_199 assump_200 =>
                            cases assump_199
                            case intro assump_201 assump_202 =>
                              apply False.elim assump_202
                      case inr assump_190 =>
                        cases assump_188
                        case intro assump_209 assump_210 =>
                          cases assump_186
                          case intro assump_215 assump_216 =>
                            cases assump_215
                            case intro assump_217 assump_218 =>
                              apply False.elim assump_218
    case inr assump_12 =>
      cases assump_10
      case intro assump_225 assump_226 =>
        cases assump_225
        case intro assump_227 assump_228 =>
          cases assump_227
          case intro assump_229 assump_230 =>
            cases assump_230
            case inl assump_233 =>
              cases assump_228
              case intro assump_237 assump_238 =>
                cases assump_226
                case intro assump_243 assump_244 =>
                  cases assump_243
                  case intro assump_245 assump_246 =>
                    cases assump_245
                    case inl assump_247 =>
                      cases assump_246
                      case intro assump_251 assump_252 =>
                        cases assump_244
                        case intro assump_257 assump_258 =>
                          cases assump_257
                          case intro assump_259 assump_260 =>
                            apply False.elim assump_260
                    case inr assump_248 =>
                      cases assump_246
                      case intro assump_267 assump_268 =>
                        cases assump_244
                        case intro assump_273 assump_274 =>
                          cases assump_273
                          case intro assump_275 assump_276 =>
                            apply False.elim assump_276
            case inr assump_234 =>
              cases assump_228
              case intro assump_283 assump_284 =>
                cases assump_226
                case intro assump_289 assump_290 =>
                  cases assump_289
                  case intro assump_291 assump_292 =>
                    cases assump_291
                    case inl assump_293 =>
                      cases assump_292
                      case intro assump_297 assump_298 =>
                        cases assump_290
                        case intro assump_303 assump_304 =>
                          cases assump_303
                          case intro assump_305 assump_306 =>
                            apply False.elim assump_306
                    case inr assump_294 =>
                      cases assump_292
                      case intro assump_313 assump_314 =>
                        cases assump_290
                        case intro assump_319 assump_320 =>
                          cases assump_319
                          case intro assump_321 assump_322 =>
                            apply False.elim assump_322


variable (p1 p7 p2 p4 p5 p0 p6 p3 : Prop)
theorem file88_29556 : (((((p5 ∧ p6) → False) → ((p4 → False) → (p4 → False))) ∨ (((p3 → p7) ∨ (p1 → False)) ∨ ((p5 → False) ∨ (p0 ∧ False)))) ∨ ((((p5 ∨ p2) ∧ (p1 → p6)) ∧ ((p5 ∧ p0) → False)) → (((False ∨ p0) ∨ (True ∨ True)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_15 : p4 := by
    exact assump_3
  let assump_11 := assump_2 assump_15
  apply False.elim assump_11


variable (p3 p6 p1 p0 p4 p5 p2 : Prop)
theorem file88_30036 : (((((p2 ∧ p5) ∨ (p0 ∧ p4)) ∧ ((False → p2) ∨ (p6 ∧ p3))) → False) → ((((True ∨ p3) ∧ (False ∧ p1)) → ((p6 → False) → (p3 → p2))) ∨ (((False ∧ False) ∨ (p4 → p4)) ∨ ((p6 ∧ True) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
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


variable (p3 p6 p5 p1 p4 : Prop)
theorem file88_30690 : (((((p4 → True) → False) ∧ ((p6 ∨ p5) → False)) → False) ∨ ((((p3 ∧ p4) ∨ (p4 → p3)) ∨ ((p1 ∧ True) ∧ (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_14 : (p4 → True) := by
      intro assump_10
      apply True.intro
    let assump_9 := assump_2 assump_14
    apply False.elim assump_9


variable (p1 p6 p5 p3 p0 p7 : Prop)
theorem file88_31121 : (((((False → False) ∨ (p1 ∨ p6)) ∧ ((p7 → False) ∨ (p5 → False))) ∧ (((True ∨ p0) → (True → False)) ∨ ((p6 ∧ p1) ∧ (p1 ∧ p6)))) → ((((False ∨ p1) → False) ∨ ((p1 → False) ∧ (p3 → False))) → (((False ∧ True) ∨ (p3 ∨ p5)) → ((True → p6) ∨ (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  case inr assump_5 =>
    cases assump_5
    case inl assump_10 =>
      cases assump_2
      case inl assump_14 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_21
              case inl assump_26 =>
                cases assump_19
                case inl assump_30 =>
                  apply Or.inl
                  intro assump_34
                  have assump_820 : (True ∨ p0) := by
                    apply Or.inl
                    apply True.intro
                  let assump_37 := assump_30 assump_820
                  have assump_821 : True := by
                    apply True.intro
                  let assump_38 := assump_37 assump_821
                  apply False.elim assump_38
                case inr assump_31 =>
                  cases assump_31
                  case intro assump_42 assump_43 =>
                    cases assump_42
                    case intro assump_44 assump_45 =>
                      cases assump_43
                      case intro assump_50 assump_51 =>
                        apply Or.inl
                        intro assump_56
                        exact assump_51
              case inr assump_27 =>
                cases assump_19
                case inl assump_61 =>
                  apply Or.inl
                  intro assump_65
                  have assump_822 : (True ∨ p0) := by
                    apply Or.inl
                    apply True.intro
                  let assump_68 := assump_61 assump_822
                  have assump_823 : True := by
                    apply True.intro
                  let assump_69 := assump_68 assump_823
                  apply False.elim assump_69
                case inr assump_62 =>
                  cases assump_62
                  case intro assump_73 assump_74 =>
                    cases assump_73
                    case intro assump_75 assump_76 =>
                      cases assump_74
                      case intro assump_81 assump_82 =>
                        apply Or.inl
                        intro assump_87
                        exact assump_82
            case inr assump_23 =>
              cases assump_23
              case inl assump_90 =>
                cases assump_21
                case inl assump_94 =>
                  cases assump_19
                  case inl assump_98 =>
                    apply Or.inl
                    intro assump_102
                    have assump_824 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_105 := assump_98 assump_824
                    have assump_825 : True := by
                      apply True.intro
                    let assump_106 := assump_105 assump_825
                    apply False.elim assump_106
                  case inr assump_99 =>
                    cases assump_99
                    case intro assump_110 assump_111 =>
                      cases assump_110
                      case intro assump_112 assump_113 =>
                        cases assump_111
                        case intro assump_118 assump_119 =>
                          apply Or.inl
                          intro assump_124
                          exact assump_119
                case inr assump_95 =>
                  cases assump_19
                  case inl assump_129 =>
                    apply Or.inl
                    intro assump_133
                    have assump_826 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_136 := assump_129 assump_826
                    have assump_827 : True := by
                      apply True.intro
                    let assump_137 := assump_136 assump_827
                    apply False.elim assump_137
                  case inr assump_130 =>
                    cases assump_130
                    case intro assump_141 assump_142 =>
                      cases assump_141
                      case intro assump_143 assump_144 =>
                        cases assump_142
                        case intro assump_149 assump_150 =>
                          apply Or.inl
                          intro assump_155
                          exact assump_150
              case inr assump_91 =>
                cases assump_21
                case inl assump_160 =>
                  cases assump_19
                  case inl assump_164 =>
                    apply Or.inl
                    intro assump_168
                    exact assump_91
                  case inr assump_165 =>
                    cases assump_165
                    case intro assump_171 assump_172 =>
                      cases assump_171
                      case intro assump_173 assump_174 =>
                        cases assump_172
                        case intro assump_179 assump_180 =>
                          apply Or.inl
                          intro assump_185
                          exact assump_180
                case inr assump_161 =>
                  cases assump_19
                  case inl assump_190 =>
                    apply Or.inl
                    intro assump_194
                    exact assump_91
                  case inr assump_191 =>
                    cases assump_191
                    case intro assump_197 assump_198 =>
                      cases assump_197
                      case intro assump_199 assump_200 =>
                        cases assump_198
                        case intro assump_205 assump_206 =>
                          apply Or.inl
                          intro assump_211
                          exact assump_206
      case inr assump_15 =>
        cases assump_15
        case intro assump_214 assump_215 =>
          cases assump_1
          case intro assump_220 assump_221 =>
            cases assump_220
            case intro assump_222 assump_223 =>
              cases assump_222
              case inl assump_224 =>
                cases assump_223
                case inl assump_228 =>
                  cases assump_221
                  case inl assump_232 =>
                    apply Or.inl
                    intro assump_236
                    have assump_828 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_239 := assump_232 assump_828
                    have assump_829 : True := by
                      apply True.intro
                    let assump_240 := assump_239 assump_829
                    apply False.elim assump_240
                  case inr assump_233 =>
                    cases assump_233
                    case intro assump_244 assump_245 =>
                      cases assump_244
                      case intro assump_246 assump_247 =>
                        cases assump_245
                        case intro assump_252 assump_253 =>
                          apply Or.inl
                          intro assump_258
                          exact assump_253
                case inr assump_229 =>
                  cases assump_221
                  case inl assump_263 =>
                    apply Or.inl
                    intro assump_267
                    have assump_830 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_270 := assump_263 assump_830
                    have assump_831 : True := by
                      apply True.intro
                    let assump_271 := assump_270 assump_831
                    apply False.elim assump_271
                  case inr assump_264 =>
                    cases assump_264
                    case intro assump_275 assump_276 =>
                      cases assump_275
                      case intro assump_277 assump_278 =>
                        cases assump_276
                        case intro assump_283 assump_284 =>
                          apply Or.inl
                          intro assump_289
                          exact assump_284
              case inr assump_225 =>
                cases assump_225
                case inl assump_292 =>
                  cases assump_223
                  case inl assump_296 =>
                    cases assump_221
                    case inl assump_300 =>
                      apply Or.inl
                      intro assump_304
                      have assump_832 : (True ∨ p0) := by
                        apply Or.inl
                        apply True.intro
                      let assump_307 := assump_300 assump_832
                      have assump_833 : True := by
                        apply True.intro
                      let assump_308 := assump_307 assump_833
                      apply False.elim assump_308
                    case inr assump_301 =>
                      cases assump_301
                      case intro assump_312 assump_313 =>
                        cases assump_312
                        case intro assump_314 assump_315 =>
                          cases assump_313
                          case intro assump_320 assump_321 =>
                            apply Or.inl
                            intro assump_326
                            exact assump_321
                  case inr assump_297 =>
                    cases assump_221
                    case inl assump_331 =>
                      apply Or.inl
                      intro assump_335
                      have assump_834 : (True ∨ p0) := by
                        apply Or.inl
                        apply True.intro
                      let assump_338 := assump_331 assump_834
                      have assump_835 : True := by
                        apply True.intro
                      let assump_339 := assump_338 assump_835
                      apply False.elim assump_339
                    case inr assump_332 =>
                      cases assump_332
                      case intro assump_343 assump_344 =>
                        cases assump_343
                        case intro assump_345 assump_346 =>
                          cases assump_344
                          case intro assump_351 assump_352 =>
                            apply Or.inl
                            intro assump_357
                            exact assump_352
                case inr assump_293 =>
                  cases assump_223
                  case inl assump_362 =>
                    cases assump_221
                    case inl assump_366 =>
                      apply Or.inl
                      intro assump_370
                      exact assump_293
                    case inr assump_367 =>
                      cases assump_367
                      case intro assump_373 assump_374 =>
                        cases assump_373
                        case intro assump_375 assump_376 =>
                          cases assump_374
                          case intro assump_381 assump_382 =>
                            apply Or.inl
                            intro assump_387
                            exact assump_382
                  case inr assump_363 =>
                    cases assump_221
                    case inl assump_392 =>
                      apply Or.inl
                      intro assump_396
                      exact assump_293
                    case inr assump_393 =>
                      cases assump_393
                      case intro assump_399 assump_400 =>
                        cases assump_399
                        case intro assump_401 assump_402 =>
                          cases assump_400
                          case intro assump_407 assump_408 =>
                            apply Or.inl
                            intro assump_413
                            exact assump_408
    case inr assump_11 =>
      cases assump_2
      case inl assump_418 =>
        cases assump_1
        case intro assump_422 assump_423 =>
          cases assump_422
          case intro assump_424 assump_425 =>
            cases assump_424
            case inl assump_426 =>
              cases assump_425
              case inl assump_430 =>
                cases assump_423
                case inl assump_434 =>
                  apply Or.inl
                  intro assump_438
                  have assump_836 : (True ∨ p0) := by
                    apply Or.inl
                    apply True.intro
                  let assump_441 := assump_434 assump_836
                  have assump_837 : True := by
                    apply True.intro
                  let assump_442 := assump_441 assump_837
                  apply False.elim assump_442
                case inr assump_435 =>
                  cases assump_435
                  case intro assump_446 assump_447 =>
                    cases assump_446
                    case intro assump_448 assump_449 =>
                      cases assump_447
                      case intro assump_454 assump_455 =>
                        apply Or.inl
                        intro assump_460
                        exact assump_455
              case inr assump_431 =>
                cases assump_423
                case inl assump_465 =>
                  apply Or.inl
                  intro assump_469
                  have assump_838 : (True ∨ p0) := by
                    apply Or.inl
                    apply True.intro
                  let assump_472 := assump_465 assump_838
                  have assump_839 : True := by
                    apply True.intro
                  let assump_473 := assump_472 assump_839
                  apply False.elim assump_473
                case inr assump_466 =>
                  cases assump_466
                  case intro assump_477 assump_478 =>
                    cases assump_477
                    case intro assump_479 assump_480 =>
                      cases assump_478
                      case intro assump_485 assump_486 =>
                        apply Or.inl
                        intro assump_491
                        exact assump_486
            case inr assump_427 =>
              cases assump_427
              case inl assump_494 =>
                cases assump_425
                case inl assump_498 =>
                  cases assump_423
                  case inl assump_502 =>
                    apply Or.inl
                    intro assump_506
                    have assump_840 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_509 := assump_502 assump_840
                    have assump_841 : True := by
                      apply True.intro
                    let assump_510 := assump_509 assump_841
                    apply False.elim assump_510
                  case inr assump_503 =>
                    cases assump_503
                    case intro assump_514 assump_515 =>
                      cases assump_514
                      case intro assump_516 assump_517 =>
                        cases assump_515
                        case intro assump_522 assump_523 =>
                          apply Or.inl
                          intro assump_528
                          exact assump_523
                case inr assump_499 =>
                  cases assump_423
                  case inl assump_533 =>
                    apply Or.inl
                    intro assump_537
                    have assump_842 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_540 := assump_533 assump_842
                    have assump_843 : True := by
                      apply True.intro
                    let assump_541 := assump_540 assump_843
                    apply False.elim assump_541
                  case inr assump_534 =>
                    cases assump_534
                    case intro assump_545 assump_546 =>
                      cases assump_545
                      case intro assump_547 assump_548 =>
                        cases assump_546
                        case intro assump_553 assump_554 =>
                          apply Or.inl
                          intro assump_559
                          exact assump_554
              case inr assump_495 =>
                cases assump_425
                case inl assump_564 =>
                  cases assump_423
                  case inl assump_568 =>
                    apply Or.inl
                    intro assump_572
                    exact assump_495
                  case inr assump_569 =>
                    cases assump_569
                    case intro assump_575 assump_576 =>
                      cases assump_575
                      case intro assump_577 assump_578 =>
                        cases assump_576
                        case intro assump_583 assump_584 =>
                          apply Or.inl
                          intro assump_589
                          exact assump_584
                case inr assump_565 =>
                  cases assump_423
                  case inl assump_594 =>
                    apply Or.inl
                    intro assump_598
                    exact assump_495
                  case inr assump_595 =>
                    cases assump_595
                    case intro assump_601 assump_602 =>
                      cases assump_601
                      case intro assump_603 assump_604 =>
                        cases assump_602
                        case intro assump_609 assump_610 =>
                          apply Or.inl
                          intro assump_615
                          exact assump_610
      case inr assump_419 =>
        cases assump_419
        case intro assump_618 assump_619 =>
          cases assump_1
          case intro assump_624 assump_625 =>
            cases assump_624
            case intro assump_626 assump_627 =>
              cases assump_626
              case inl assump_628 =>
                cases assump_627
                case inl assump_632 =>
                  cases assump_625
                  case inl assump_636 =>
                    apply Or.inl
                    intro assump_640
                    have assump_844 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_643 := assump_636 assump_844
                    have assump_845 : True := by
                      apply True.intro
                    let assump_644 := assump_643 assump_845
                    apply False.elim assump_644
                  case inr assump_637 =>
                    cases assump_637
                    case intro assump_648 assump_649 =>
                      cases assump_648
                      case intro assump_650 assump_651 =>
                        cases assump_649
                        case intro assump_656 assump_657 =>
                          apply Or.inl
                          intro assump_662
                          exact assump_657
                case inr assump_633 =>
                  cases assump_625
                  case inl assump_667 =>
                    apply Or.inl
                    intro assump_671
                    have assump_846 : (True ∨ p0) := by
                      apply Or.inl
                      apply True.intro
                    let assump_674 := assump_667 assump_846
                    have assump_847 : True := by
                      apply True.intro
                    let assump_675 := assump_674 assump_847
                    apply False.elim assump_675
                  case inr assump_668 =>
                    cases assump_668
                    case intro assump_679 assump_680 =>
                      cases assump_679
                      case intro assump_681 assump_682 =>
                        cases assump_680
                        case intro assump_687 assump_688 =>
                          apply Or.inl
                          intro assump_693
                          exact assump_688
              case inr assump_629 =>
                cases assump_629
                case inl assump_696 =>
                  cases assump_627
                  case inl assump_700 =>
                    cases assump_625
                    case inl assump_704 =>
                      apply Or.inl
                      intro assump_708
                      have assump_848 : (True ∨ p0) := by
                        apply Or.inl
                        apply True.intro
                      let assump_711 := assump_704 assump_848
                      have assump_849 : True := by
                        apply True.intro
                      let assump_712 := assump_711 assump_849
                      apply False.elim assump_712
                    case inr assump_705 =>
                      cases assump_705
                      case intro assump_716 assump_717 =>
                        cases assump_716
                        case intro assump_718 assump_719 =>
                          cases assump_717
                          case intro assump_724 assump_725 =>
                            apply Or.inl
                            intro assump_730
                            exact assump_725
                  case inr assump_701 =>
                    cases assump_625
                    case inl assump_735 =>
                      apply Or.inl
                      intro assump_739
                      have assump_850 : (True ∨ p0) := by
                        apply Or.inl
                        apply True.intro
                      let assump_742 := assump_735 assump_850
                      have assump_851 : True := by
                        apply True.intro
                      let assump_743 := assump_742 assump_851
                      apply False.elim assump_743
                    case inr assump_736 =>
                      cases assump_736
                      case intro assump_747 assump_748 =>
                        cases assump_747
                        case intro assump_749 assump_750 =>
                          cases assump_748
                          case intro assump_755 assump_756 =>
                            apply Or.inl
                            intro assump_761
                            exact assump_756
                case inr assump_697 =>
                  cases assump_627
                  case inl assump_766 =>
                    cases assump_625
                    case inl assump_770 =>
                      apply Or.inl
                      intro assump_774
                      exact assump_697
                    case inr assump_771 =>
                      cases assump_771
                      case intro assump_777 assump_778 =>
                        cases assump_777
                        case intro assump_779 assump_780 =>
                          cases assump_778
                          case intro assump_785 assump_786 =>
                            apply Or.inl
                            intro assump_791
                            exact assump_786
                  case inr assump_767 =>
                    cases assump_625
                    case inl assump_796 =>
                      apply Or.inl
                      intro assump_800
                      exact assump_697
                    case inr assump_797 =>
                      cases assump_797
                      case intro assump_803 assump_804 =>
                        cases assump_803
                        case intro assump_805 assump_806 =>
                          cases assump_804
                          case intro assump_811 assump_812 =>
                            apply Or.inl
                            intro assump_817
                            exact assump_812


variable (p2 p4 p3 p1 p7 p6 p0 : Prop)
theorem file88_55765 : (((((p3 ∨ True) ∨ (p2 → p4)) ∨ ((p0 ∧ True) → False)) ∨ (((p6 → False) ∧ (p4 → p4)) → False)) ∨ ((((p3 → False) ∨ (p4 ∨ p1)) → ((p2 → p2) ∨ (p2 ∨ p1))) ∨ (((False → p6) ∨ (p7 → p7)) ∨ ((p4 ∧ True) ∨ (p3 ∨ p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p2 p0 p1 p4 p6 p3 p7 : Prop)
theorem file88_56141 : ((((((False ∧ False) ∧ (True ∨ p7)) ∧ ((p1 → p0) → False)) → (((False ∨ False) → (p4 ∨ p2)) → False)) → ((((p3 ∨ p4) ∨ (p2 → True)) ∨ ((p6 → False) ∨ (p6 → p6))) → False)) → False) := by
  intro assump_1
  have assump_22 : ((((False ∧ False) ∧ (True ∨ p7)) ∧ ((p1 → p0) → False)) → (((False ∨ False) → (p4 ∨ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_22
  have assump_23 : (((p3 ∨ p4) ∨ (p2 → True)) ∨ ((p6 → False) ∨ (p6 → p6))) := by
    apply Or.inl
    apply Or.inr
    intro assump_18
    apply True.intro
  let assump_17 := assump_4 assump_23
  apply False.elim assump_17


variable (p3 p0 p6 p2 p5 p7 p4 : Prop)
theorem file88_57052 : (((((True → False) ∧ (p2 → p6)) → False) ∨ (((True → False) → False) ∧ ((p2 ∧ p0) ∨ (p3 → p6)))) ∨ ((((p6 → False) ∧ (p4 ∧ p5)) → False) ∧ (((p4 → False) → False) → ((p7 ∨ p3) ∧ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : True := by
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p4 p1 p3 p5 p0 p6 p7 : Prop)
theorem file88_57538 : ((((((p6 ∧ p5) ∨ (p5 ∨ p6)) ∨ ((p7 ∧ p3) ∧ (p1 ∨ p1))) ∨ (((False ∧ p5) ∨ (p4 ∧ False)) → ((p4 ∨ p0) → (p4 ∧ p0)))) ∧ ((((p4 ∨ False) → False) ∨ ((False → p3) → False)) ∧ (((p5 → False) → (p5 → False)) → False))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_12
            case intro assump_25 assump_26 =>
              cases assump_25
              case inl assump_27 =>
                have assump_287 : ((p5 → False) → (p5 → False)) := by
                  intro assump_34
                  intro assump_35
                  have assump_288 : p5 := by
                    exact assump_35
                  let assump_40 := assump_34 assump_288
                  apply False.elim assump_40
                let assump_33 := assump_26 assump_287
                apply False.elim assump_33
              case inr assump_28 =>
                have assump_289 : ((p5 → False) → (p5 → False)) := by
                  intro assump_52
                  intro assump_53
                  have assump_290 : p5 := by
                    exact assump_53
                  let assump_58 := assump_52 assump_290
                  apply False.elim assump_58
                let assump_51 := assump_26 assump_289
                apply False.elim assump_51
        case inr assump_18 =>
          cases assump_18
          case inl assump_65 =>
            cases assump_12
            case intro assump_69 assump_70 =>
              cases assump_69
              case inl assump_71 =>
                have assump_291 : ((p5 → False) → (p5 → False)) := by
                  intro assump_78
                  intro assump_79
                  have assump_292 : p5 := by
                    exact assump_79
                  let assump_84 := assump_78 assump_292
                  apply False.elim assump_84
                let assump_77 := assump_70 assump_291
                apply False.elim assump_77
              case inr assump_72 =>
                have assump_293 : ((p5 → False) → (p5 → False)) := by
                  intro assump_96
                  intro assump_97
                  have assump_294 : p5 := by
                    exact assump_97
                  let assump_102 := assump_96 assump_294
                  apply False.elim assump_102
                let assump_95 := assump_70 assump_293
                apply False.elim assump_95
          case inr assump_66 =>
            cases assump_12
            case intro assump_111 assump_112 =>
              cases assump_111
              case inl assump_113 =>
                have assump_295 : ((p5 → False) → (p5 → False)) := by
                  intro assump_120
                  intro assump_121
                  have assump_296 : p5 := by
                    exact assump_121
                  let assump_126 := assump_120 assump_296
                  apply False.elim assump_126
                let assump_119 := assump_112 assump_295
                apply False.elim assump_119
              case inr assump_114 =>
                have assump_297 : ((p5 → False) → (p5 → False)) := by
                  intro assump_138
                  intro assump_139
                  have assump_298 : p5 := by
                    exact assump_139
                  let assump_144 := assump_138 assump_298
                  apply False.elim assump_144
                let assump_137 := assump_112 assump_297
                apply False.elim assump_137
      case inr assump_16 =>
        cases assump_16
        case intro assump_151 assump_152 =>
          cases assump_151
          case intro assump_153 assump_154 =>
            cases assump_152
            case inl assump_159 =>
              cases assump_12
              case intro assump_163 assump_164 =>
                cases assump_163
                case inl assump_165 =>
                  have assump_299 : ((p5 → False) → (p5 → False)) := by
                    intro assump_172
                    intro assump_173
                    have assump_300 : p5 := by
                      exact assump_173
                    let assump_178 := assump_172 assump_300
                    apply False.elim assump_178
                  let assump_171 := assump_164 assump_299
                  apply False.elim assump_171
                case inr assump_166 =>
                  have assump_301 : ((p5 → False) → (p5 → False)) := by
                    intro assump_190
                    intro assump_191
                    have assump_302 : p5 := by
                      exact assump_191
                    let assump_196 := assump_190 assump_302
                    apply False.elim assump_196
                  let assump_189 := assump_164 assump_301
                  apply False.elim assump_189
            case inr assump_160 =>
              cases assump_12
              case intro assump_205 assump_206 =>
                cases assump_205
                case inl assump_207 =>
                  have assump_303 : ((p5 → False) → (p5 → False)) := by
                    intro assump_214
                    intro assump_215
                    have assump_304 : p5 := by
                      exact assump_215
                    let assump_220 := assump_214 assump_304
                    apply False.elim assump_220
                  let assump_213 := assump_206 assump_303
                  apply False.elim assump_213
                case inr assump_208 =>
                  have assump_305 : ((p5 → False) → (p5 → False)) := by
                    intro assump_232
                    intro assump_233
                    have assump_306 : p5 := by
                      exact assump_233
                    let assump_238 := assump_232 assump_306
                    apply False.elim assump_238
                  let assump_231 := assump_206 assump_305
                  apply False.elim assump_231
    case inr assump_14 =>
      cases assump_12
      case intro assump_247 assump_248 =>
        cases assump_247
        case inl assump_249 =>
          have assump_307 : ((p5 → False) → (p5 → False)) := by
            intro assump_256
            intro assump_257
            have assump_308 : p5 := by
              exact assump_257
            let assump_262 := assump_256 assump_308
            apply False.elim assump_262
          let assump_255 := assump_248 assump_307
          apply False.elim assump_255
        case inr assump_250 =>
          have assump_309 : ((p5 → False) → (p5 → False)) := by
            intro assump_274
            intro assump_275
            have assump_310 : p5 := by
              exact assump_275
            let assump_280 := assump_274 assump_310
            apply False.elim assump_280
          let assump_273 := assump_248 assump_309
          apply False.elim assump_273


variable (p5 p6 p3 p1 p7 p4 : Prop)
theorem file88_64640 : ((((((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) → False) ∧ ((((p3 ∧ p4) ∨ (p7 ∧ p1)) ∨ ((p6 → True) ∧ (p5 → False))) ∧ (((p7 ∨ p5) → False) ∨ ((p6 ∨ p6) → (p1 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_18 =>
              have assump_322 : (((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) := by
                intro assump_26
                apply And.intro
                intro assump_27
                cases assump_26
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case inl assump_32 =>
                    cases assump_31
                    case inl assump_36 =>
                      apply False.elim assump_36
                    case inr assump_37 =>
                      apply False.elim assump_37
                  case inr assump_33 =>
                    cases assump_31
                    case inl assump_44 =>
                      apply False.elim assump_44
                    case inr assump_45 =>
                      apply False.elim assump_45
                intro assump_50
                cases assump_26
                case intro assump_53 assump_54 =>
                  cases assump_53
                  case inl assump_55 =>
                    cases assump_54
                    case inl assump_59 =>
                      apply False.elim assump_59
                    case inr assump_60 =>
                      apply False.elim assump_60
                  case inr assump_56 =>
                    cases assump_54
                    case inl assump_67 =>
                      apply False.elim assump_67
                    case inr assump_68 =>
                      apply False.elim assump_68
              let assump_25 := assump_2 assump_322
              apply False.elim assump_25
            case inr assump_19 =>
              have assump_323 : (((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) := by
                intro assump_82
                apply And.intro
                intro assump_83
                cases assump_82
                case intro assump_86 assump_87 =>
                  cases assump_86
                  case inl assump_88 =>
                    cases assump_87
                    case inl assump_92 =>
                      apply False.elim assump_92
                    case inr assump_93 =>
                      apply False.elim assump_93
                  case inr assump_89 =>
                    cases assump_87
                    case inl assump_100 =>
                      apply False.elim assump_100
                    case inr assump_101 =>
                      apply False.elim assump_101
                intro assump_106
                cases assump_82
                case intro assump_109 assump_110 =>
                  cases assump_109
                  case inl assump_111 =>
                    cases assump_110
                    case inl assump_115 =>
                      apply False.elim assump_115
                    case inr assump_116 =>
                      apply False.elim assump_116
                  case inr assump_112 =>
                    cases assump_110
                    case inl assump_123 =>
                      apply False.elim assump_123
                    case inr assump_124 =>
                      apply False.elim assump_124
              let assump_81 := assump_2 assump_323
              apply False.elim assump_81
        case inr assump_11 =>
          cases assump_11
          case intro assump_132 assump_133 =>
            cases assump_7
            case inl assump_138 =>
              have assump_324 : (p7 ∨ p5) := by
                apply Or.inl
                exact assump_132
              let assump_142 := assump_138 assump_324
              apply False.elim assump_142
            case inr assump_139 =>
              have assump_325 : (((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) := by
                intro assump_152
                apply And.intro
                intro assump_153
                cases assump_152
                case intro assump_156 assump_157 =>
                  cases assump_156
                  case inl assump_158 =>
                    cases assump_157
                    case inl assump_162 =>
                      apply False.elim assump_162
                    case inr assump_163 =>
                      apply False.elim assump_163
                  case inr assump_159 =>
                    cases assump_157
                    case inl assump_170 =>
                      apply False.elim assump_170
                    case inr assump_171 =>
                      apply False.elim assump_171
                intro assump_176
                cases assump_152
                case intro assump_179 assump_180 =>
                  cases assump_179
                  case inl assump_181 =>
                    cases assump_180
                    case inl assump_185 =>
                      apply False.elim assump_185
                    case inr assump_186 =>
                      apply False.elim assump_186
                  case inr assump_182 =>
                    cases assump_180
                    case inl assump_193 =>
                      apply False.elim assump_193
                    case inr assump_194 =>
                      apply False.elim assump_194
              let assump_151 := assump_2 assump_325
              apply False.elim assump_151
      case inr assump_9 =>
        cases assump_9
        case intro assump_202 assump_203 =>
          cases assump_7
          case inl assump_208 =>
            have assump_326 : (((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) := by
              intro assump_216
              apply And.intro
              intro assump_217
              cases assump_216
              case intro assump_220 assump_221 =>
                cases assump_220
                case inl assump_222 =>
                  cases assump_221
                  case inl assump_226 =>
                    apply False.elim assump_226
                  case inr assump_227 =>
                    apply False.elim assump_227
                case inr assump_223 =>
                  cases assump_221
                  case inl assump_234 =>
                    apply False.elim assump_234
                  case inr assump_235 =>
                    apply False.elim assump_235
              intro assump_240
              cases assump_216
              case intro assump_243 assump_244 =>
                cases assump_243
                case inl assump_245 =>
                  cases assump_244
                  case inl assump_249 =>
                    apply False.elim assump_249
                  case inr assump_250 =>
                    apply False.elim assump_250
                case inr assump_246 =>
                  cases assump_244
                  case inl assump_257 =>
                    apply False.elim assump_257
                  case inr assump_258 =>
                    apply False.elim assump_258
            let assump_215 := assump_2 assump_326
            apply False.elim assump_215
          case inr assump_209 =>
            have assump_327 : (((p6 ∨ p1) ∧ (False ∨ False)) → ((p7 → False) ∧ (True → p3))) := by
              intro assump_272
              apply And.intro
              intro assump_273
              cases assump_272
              case intro assump_276 assump_277 =>
                cases assump_276
                case inl assump_278 =>
                  cases assump_277
                  case inl assump_282 =>
                    apply False.elim assump_282
                  case inr assump_283 =>
                    apply False.elim assump_283
                case inr assump_279 =>
                  cases assump_277
                  case inl assump_290 =>
                    apply False.elim assump_290
                  case inr assump_291 =>
                    apply False.elim assump_291
              intro assump_296
              cases assump_272
              case intro assump_299 assump_300 =>
                cases assump_299
                case inl assump_301 =>
                  cases assump_300
                  case inl assump_305 =>
                    apply False.elim assump_305
                  case inr assump_306 =>
                    apply False.elim assump_306
                case inr assump_302 =>
                  cases assump_300
                  case inl assump_313 =>
                    apply False.elim assump_313
                  case inr assump_314 =>
                    apply False.elim assump_314
            let assump_271 := assump_2 assump_327
            apply False.elim assump_271


variable (p3 p2 p1 p7 p0 p6 p4 p5 : Prop)
theorem file88_73795 : (((((p7 ∧ p5) ∧ (p3 ∨ p6)) → ((p7 → p2) ∨ (p6 ∨ p0))) ∧ (((p0 → p5) ∨ (True ∧ False)) ∧ ((p7 ∧ p1) ∧ (p1 → p4)))) → ((((True → False) → False) → ((p0 ∧ p2) → False)) → (((False ∧ p3) ∧ (True → p1)) → ((p1 ∧ p3) ∧ (p5 → p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  cases assump_3
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  intro assump_16
  cases assump_3
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      apply False.elim assump_21


variable (p1 p5 p2 p3 p0 p7 p6 p4 : Prop)
theorem file88_74625 : ((((((p6 → p4) → (p6 ∧ p5)) → False) → (((p5 ∧ p5) ∧ (True → False)) → ((p7 ∨ p3) → (p0 ∨ p6)))) ∧ ((((False ∧ p6) → False) ∨ ((p6 → False) ∨ (False → False))) → (((p2 → p5) ∧ (True → False)) ∧ ((p1 ∨ p2) → (p7 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((False ∧ p6) → False) ∨ ((p6 → False) ∨ (False → False))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_3 assump_21
    let assump_14 := And.left assump_8
    let assump_15 := And.right assump_14
    have assump_22 : True := by
      apply True.intro
    let assump_17 := assump_15 assump_22
    apply False.elim assump_17


variable (p3 p5 p4 p6 p7 p1 : Prop)
theorem file88_75458 : ((((((p1 → False) ∧ (p6 ∧ p7)) ∨ ((p4 → p4) → (p5 → p3))) → False) ∧ ((((p7 → False) ∨ (p4 ∨ p7)) → False) ∧ (((False ∧ p6) → (p6 ∨ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_21 : ((False ∧ p6) → (p6 ∨ p7)) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      let assump_12 := assump_7 assump_21
      apply False.elim assump_12


variable (p7 p3 p2 p0 p5 p1 : Prop)
theorem file88_76062 : ((((((p5 ∨ p7) → False) → False) ∧ (((p7 → False) ∨ (p3 ∧ p1)) ∨ ((True ∨ p5) ∨ (False ∧ p7)))) ∧ ((((p0 → False) ∨ (p0 ∨ p7)) → ((p2 ∧ p2) → False)) ∧ (((False → False) ∧ (p3 → True)) → False))) → False) := by
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
            have assump_88 : ((False → False) ∧ (p3 → True)) := by
              apply And.intro
              intro assump_21
              apply False.elim assump_21
              intro assump_24
              apply True.intro
            let assump_20 := assump_15 assump_88
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case intro assump_28 assump_29 =>
            cases assump_3
            case intro assump_34 assump_35 =>
              have assump_89 : ((False → False) ∧ (p3 → True)) := by
                apply And.intro
                intro assump_41
                apply False.elim assump_41
                intro assump_44
                apply True.intro
              let assump_40 := assump_35 assump_89
              apply False.elim assump_40
      case inr assump_9 =>
        cases assump_9
        case inl assump_48 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_3
            case intro assump_54 assump_55 =>
              have assump_90 : ((False → False) ∧ (p3 → True)) := by
                apply And.intro
                intro assump_61
                apply False.elim assump_61
                intro assump_64
                apply True.intro
              let assump_60 := assump_55 assump_90
              apply False.elim assump_60
          case inr assump_51 =>
            cases assump_3
            case intro assump_70 assump_71 =>
              have assump_91 : ((False → False) ∧ (p3 → True)) := by
                apply And.intro
                intro assump_77
                apply False.elim assump_77
                intro assump_80
                apply True.intro
              let assump_76 := assump_71 assump_91
              apply False.elim assump_76
        case inr assump_49 =>
          cases assump_49
          case intro assump_84 assump_85 =>
            apply False.elim assump_84


variable (p0 p3 p2 p4 p6 p7 p5 p1 : Prop)
theorem file88_78576 : (((((p7 → False) ∧ (p6 ∧ False)) ∧ ((p7 ∧ False) ∨ (p2 ∨ True))) → (((p1 ∧ p6) → (False ∧ p0)) → False)) ∨ ((((True ∨ p4) ∨ (p2 ∧ p6)) → ((True ∧ True) ∧ (p5 → False))) ∨ (((False ∧ p7) ∨ (p0 ∧ p3)) ∧ ((p4 → False) → (p7 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_12


variable (p3 p5 p6 p7 p4 : Prop)
theorem file88_79121 : ((((((p6 → False) ∧ (p6 → p5)) → ((True ∨ p5) → (p4 ∨ p7))) → (((p5 ∧ False) ∨ (False ∧ p5)) → ((p6 → p3) ∧ (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p6 → False) ∧ (p6 → p5)) → ((True ∨ p5) → (p4 ∨ p7))) → (((p5 ∧ False) ∨ (False ∧ p5)) → ((p6 → p3) ∧ (p3 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
    case inr assump_11 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
    intro assump_22
    cases assump_6
    case inl assump_25 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_28
    case inr assump_26 =>
      cases assump_26
      case intro assump_33 assump_34 =>
        apply False.elim assump_33
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p4 p7 p3 p1 p5 p2 : Prop)
theorem file88_80185 : ((((((p2 ∧ p2) → (False → False)) ∨ ((p2 ∧ False) → (p2 ∧ True))) ∧ (((False → False) → False) ∧ ((p2 ∧ p4) ∧ (True ∧ p4)))) ∧ ((((p4 ∧ False) ∧ (p2 ∧ True)) ∧ ((False ∧ p2) → False)) ∧ (((p7 ∧ p5) → False) ∧ ((p3 → False) ∧ (p1 ∨ p5))))) → False) := by
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
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_3
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        apply False.elim assump_35
      case inr assump_7 =>
        cases assump_5
        case intro assump_42 assump_43 =>
          cases assump_43
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              cases assump_47
              case intro assump_54 assump_55 =>
                cases assump_3
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case intro assump_64 assump_65 =>
                      cases assump_64
                      case intro assump_66 assump_67 =>
                        apply False.elim assump_67


variable (p3 p4 p1 p2 p7 : Prop)
theorem file88_82072 : ((((((p4 ∧ False) → False) ∧ ((False → p3) ∨ (p2 ∨ p1))) ∨ (((p4 → p2) ∧ (True → p3)) ∨ ((True → p4) ∧ (p7 → p2)))) → False) → False) := by
  intro assump_5
  have assump_22 : ((((p4 ∧ False) → False) ∧ ((False → p3) ∨ (p2 ∨ p1))) ∨ (((p4 → p2) ∧ (True → p3)) ∨ ((True → p4) ∧ (p7 → p2)))) := by
    apply Or.inl
    apply And.intro
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
    apply Or.inl
    intro assump_16
    apply False.elim assump_16
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p5 p3 p0 : Prop)
theorem file88_82698 : ((((((p0 ∧ p0) → False) ∨ ((p3 ∨ p5) → (p5 ∧ p0))) → False) ∧ ((((p5 ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p5 ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (p5 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p3 p7 p6 : Prop)
theorem file88_83251 : (((((False → p3) → False) ∨ ((p7 ∧ False) ∧ (p3 → p1))) ∨ (((p1 ∧ p1) ∨ (False ∧ p3)) ∧ ((False → False) → False))) → ((((p3 → p6) ∨ (p1 → False)) → False) → (((p6 → False) ∧ (p7 ∨ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      cases assump_1
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          have assump_60 : (False → p3) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_16 assump_60
          apply False.elim assump_20
        case inr assump_17 =>
          cases assump_17
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              apply False.elim assump_30
      case inr assump_15 =>
        cases assump_15
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              have assump_61 : (False → False) := by
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_36 assump_61
              apply False.elim assump_47
          case inr assump_38 =>
            cases assump_38
            case intro assump_54 assump_55 =>
              apply False.elim assump_54
    case inr assump_9 =>
      apply False.elim assump_9


variable (p7 p6 p0 p5 p2 p4 p3 p1 : Prop)
theorem file88_84834 : (((((p7 ∨ p4) ∧ (p4 ∧ p7)) → False) → (((p7 ∨ p3) → (p4 ∧ p2)) → ((False → False) ∨ (p1 ∨ p5)))) ∨ ((((p6 → False) → (p1 → p3)) → False) ∨ (((p0 → p7) → (p6 ∨ True)) ∧ ((p2 → False) → (p2 → True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p3 p4 p1 p2 p6 p0 : Prop)
theorem file88_85209 : ((((((p2 → p2) → (p3 → p0)) → False) ∧ (((True → False) → (False → False)) ∧ ((True ∧ p6) ∧ (False → p6)))) ∧ ((((p4 → False) → False) → ((True → p1) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_33 : (((p4 → False) → False) → ((True → p1) → (False → False))) := by
              intro assump_25
              intro assump_26
              intro assump_27
              apply False.elim assump_27
            let assump_24 := assump_3 assump_33
            apply False.elim assump_24


variable (p4 p2 p6 p7 p5 : Prop)
theorem file88_86090 : ((((((p5 ∨ p2) ∨ (p6 → True)) ∨ ((p2 ∧ p7) → False)) ∨ (((p7 → False) ∧ (True ∨ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p5 ∨ p2) ∨ (p6 → True)) ∨ ((p2 ∧ p7) → False)) ∨ (((p7 → False) ∧ (True ∨ p4)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p0 p6 p5 : Prop)
theorem file88_86552 : ((((((p3 ∨ p0) → (p5 → False)) ∨ ((p6 → p5) → False)) → False) ∧ ((((p6 → False) ∧ (p0 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p6 → False) ∧ (p0 ∧ False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p2 p3 p0 p1 : Prop)
theorem file88_87126 : ((((((p1 ∨ True) → False) → False) ∨ (((p3 ∧ p3) ∨ (p2 ∨ p0)) ∧ ((p0 ∧ p1) ∨ (False → True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p1 ∨ True) → False) → False) ∨ (((p3 ∧ p3) ∨ (p2 ∨ p0)) ∧ ((p0 ∧ p1) ∨ (False → True)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p3 p1 p0 : Prop)
theorem file88_87685 : (((((False ∧ p0) ∧ (p4 → False)) ∧ ((p4 ∧ p1) ∨ (False ∧ False))) → (((p3 ∨ False) → (p1 ∨ False)) → ((p4 → p3) ∨ (p1 ∧ p3)))) ∨ ((((p0 ∨ p1) → False) ∨ ((p1 ∧ p0) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p6 p4 p7 p0 p5 p3 : Prop)
theorem file88_88184 : ((((((True ∧ p0) ∨ (True ∨ p4)) → ((p4 ∧ p7) ∧ (p6 ∧ False))) → (((p7 ∨ p6) ∨ (p5 → p4)) ∧ ((False → p7) ∧ (p3 → p3)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((True ∧ p0) ∨ (True ∨ p4)) → ((p4 ∧ p7) ∧ (p6 ∧ False))) → (((p7 ∨ p6) ∨ (p5 → p4)) ∧ ((False → p7) ∧ (p3 → p3)))) := by
    intro assump_5
    apply And.intro
    apply Or.inr
    intro assump_8
    have assump_28 : ((True ∧ p0) ∨ (True ∨ p4)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_12 := assump_5 assump_28
    let assump_13 := And.left assump_12
    let assump_14 := And.left assump_13
    exact assump_14
    apply And.intro
    intro assump_16
    apply False.elim assump_16
    intro assump_19
    exact assump_19
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p7 p5 p1 p3 p2 p6 p0 : Prop)
theorem file88_89058 : (((((p5 ∨ p2) ∨ (False → p7)) ∨ ((p3 → False) → False)) ∨ (((p3 ∧ p7) ∧ (p7 ∧ p0)) → ((p1 ∧ p6) ∧ (True ∧ p2)))) ∨ ((((p3 → False) → False) → ((p2 → p5) → (p2 ∧ p6))) → (((True → False) → (p3 ∧ p5)) ∨ ((p5 → p1) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1


variable (p4 p6 p3 p7 p2 p5 p1 p0 : Prop)
theorem file88_89459 : (((((p0 ∧ False) → (p2 → p3)) ∧ ((p7 ∧ p1) ∧ (p3 → p7))) ∧ (((True ∧ p7) ∧ (p7 ∧ p4)) ∨ ((p4 ∧ p4) ∧ (p3 ∨ p4)))) → ((((p1 → False) → False) ∧ ((p7 → p1) → False)) → (((p0 → False) ∧ (p6 → p5)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case intro assump_10 assump_11 =>
      cases assump_1
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_19
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              cases assump_17
              case inl assump_32 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  cases assump_34
                  case intro assump_36 assump_37 =>
                    cases assump_35
                    case intro assump_42 assump_43 =>
                      have assump_105 : (p7 → p1) := by
                        intro assump_56
                        exact assump_25
                      let assump_55 := assump_11 assump_105
                      apply False.elim assump_55
              case inr assump_33 =>
                cases assump_33
                case intro assump_62 assump_63 =>
                  cases assump_62
                  case intro assump_64 assump_65 =>
                    cases assump_63
                    case inl assump_70 =>
                      have assump_106 : (p7 → p1) := by
                        intro assump_83
                        exact assump_25
                      let assump_82 := assump_11 assump_106
                      apply False.elim assump_82
                    case inr assump_71 =>
                      have assump_107 : (p7 → p1) := by
                        intro assump_99
                        exact assump_25
                      let assump_98 := assump_11 assump_107
                      apply False.elim assump_98


variable (p7 p2 p4 p0 p6 p1 p5 p3 : Prop)
theorem file88_91549 : ((((((p4 → p7) → False) → ((p3 → False) ∧ (p6 ∧ p7))) ∧ (((p4 ∨ p5) ∧ (p2 ∧ p6)) ∧ ((p4 → p1) → (p5 ∧ p5)))) ∧ ((((p7 ∧ False) ∧ (False ∨ p3)) ∨ ((p3 ∧ p4) → (p0 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              have assump_66 : (((p7 ∧ False) ∧ (False ∨ p3)) ∨ ((p3 ∧ p4) → (p0 → p2))) := by
                apply Or.inr
                intro assump_27
                intro assump_28
                cases assump_27
                case intro assump_31 assump_32 =>
                  exact assump_16
              let assump_26 := assump_3 assump_66
              apply False.elim assump_26
          case inr assump_13 =>
            cases assump_11
            case intro assump_42 assump_43 =>
              have assump_67 : (((p7 ∧ False) ∧ (False ∨ p3)) ∨ ((p3 ∧ p4) → (p0 → p2))) := by
                apply Or.inr
                intro assump_53
                intro assump_54
                cases assump_53
                case intro assump_57 assump_58 =>
                  exact assump_42
              let assump_52 := assump_3 assump_67
              apply False.elim assump_52


variable (p3 p2 p4 p5 p1 p6 p7 p0 : Prop)
theorem file88_93085 : ((((((p4 ∨ p6) ∨ (p5 → False)) ∨ ((p6 ∨ p7) → (p2 → False))) ∨ (((p0 → False) → False) ∧ ((True ∧ p0) ∧ (p1 → False)))) ∧ ((((p1 ∧ p4) ∧ (p3 → False)) ∧ ((p1 ∨ p3) ∨ (p3 ∧ p0))) ∧ (((p6 ∨ p1) ∨ (p4 → p7)) → False))) → False) := by
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
              case intro assump_16 assump_17 =>
                cases assump_16
                case intro assump_18 assump_19 =>
                  cases assump_18
                  case intro assump_20 assump_21 =>
                    cases assump_17
                    case inl assump_28 =>
                      cases assump_28
                      case inl assump_30 =>
                        have assump_264 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_30
                        let assump_36 := assump_15 assump_264
                        apply False.elim assump_36
                      case inr assump_31 =>
                        have assump_265 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_20
                        let assump_44 := assump_15 assump_265
                        apply False.elim assump_44
                    case inr assump_29 =>
                      cases assump_29
                      case intro assump_48 assump_49 =>
                        have assump_266 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_20
                        let assump_56 := assump_15 assump_266
                        apply False.elim assump_56
          case inr assump_11 =>
            cases assump_3
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case intro assump_68 assump_69 =>
                    cases assump_65
                    case inl assump_76 =>
                      cases assump_76
                      case inl assump_78 =>
                        have assump_267 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_11
                        let assump_84 := assump_63 assump_267
                        apply False.elim assump_84
                      case inr assump_79 =>
                        have assump_268 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_11
                        let assump_92 := assump_63 assump_268
                        apply False.elim assump_92
                    case inr assump_77 =>
                      cases assump_77
                      case intro assump_96 assump_97 =>
                        have assump_269 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inl
                          exact assump_11
                        let assump_104 := assump_63 assump_269
                        apply False.elim assump_104
        case inr assump_9 =>
          cases assump_3
          case intro assump_110 assump_111 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              cases assump_112
              case intro assump_114 assump_115 =>
                cases assump_114
                case intro assump_116 assump_117 =>
                  cases assump_113
                  case inl assump_124 =>
                    cases assump_124
                    case inl assump_126 =>
                      have assump_270 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                        apply Or.inl
                        apply Or.inr
                        exact assump_126
                      let assump_132 := assump_111 assump_270
                      apply False.elim assump_132
                    case inr assump_127 =>
                      have assump_271 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                        apply Or.inl
                        apply Or.inr
                        exact assump_116
                      let assump_140 := assump_111 assump_271
                      apply False.elim assump_140
                  case inr assump_125 =>
                    cases assump_125
                    case intro assump_144 assump_145 =>
                      have assump_272 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                        apply Or.inl
                        apply Or.inr
                        exact assump_116
                      let assump_152 := assump_111 assump_272
                      apply False.elim assump_152
      case inr assump_7 =>
        cases assump_3
        case intro assump_158 assump_159 =>
          cases assump_158
          case intro assump_160 assump_161 =>
            cases assump_160
            case intro assump_162 assump_163 =>
              cases assump_162
              case intro assump_164 assump_165 =>
                cases assump_161
                case inl assump_172 =>
                  cases assump_172
                  case inl assump_174 =>
                    have assump_273 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                      apply Or.inl
                      apply Or.inr
                      exact assump_174
                    let assump_180 := assump_159 assump_273
                    apply False.elim assump_180
                  case inr assump_175 =>
                    have assump_274 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                      apply Or.inl
                      apply Or.inr
                      exact assump_164
                    let assump_188 := assump_159 assump_274
                    apply False.elim assump_188
                case inr assump_173 =>
                  cases assump_173
                  case intro assump_192 assump_193 =>
                    have assump_275 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                      apply Or.inl
                      apply Or.inr
                      exact assump_164
                    let assump_200 := assump_159 assump_275
                    apply False.elim assump_200
    case inr assump_5 =>
      cases assump_5
      case intro assump_204 assump_205 =>
        cases assump_205
        case intro assump_208 assump_209 =>
          cases assump_208
          case intro assump_210 assump_211 =>
            cases assump_3
            case intro assump_218 assump_219 =>
              cases assump_218
              case intro assump_220 assump_221 =>
                cases assump_220
                case intro assump_222 assump_223 =>
                  cases assump_222
                  case intro assump_224 assump_225 =>
                    cases assump_221
                    case inl assump_232 =>
                      cases assump_232
                      case inl assump_234 =>
                        have assump_276 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_234
                        let assump_240 := assump_219 assump_276
                        apply False.elim assump_240
                      case inr assump_235 =>
                        have assump_277 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_224
                        let assump_248 := assump_219 assump_277
                        apply False.elim assump_248
                    case inr assump_233 =>
                      cases assump_233
                      case intro assump_252 assump_253 =>
                        have assump_278 : ((p6 ∨ p1) ∨ (p4 → p7)) := by
                          apply Or.inl
                          apply Or.inr
                          exact assump_224
                        let assump_260 := assump_219 assump_278
                        apply False.elim assump_260


variable (p5 p0 p4 p2 p3 : Prop)
theorem file88_101724 : (((((True ∨ p2) → False) → ((p3 ∧ True) ∨ (False → p2))) ∧ (((p4 → False) ∧ (p0 → False)) ∧ ((p2 → False) ∨ (p5 ∨ True)))) → ((((p4 ∨ True) ∨ (p4 → False)) → ((True ∧ p4) → (True ∧ p0))) → (((p5 → False) → False) → ((p3 ∧ p4) → (p0 ∧ p2))))) := by
  intro assump_25
  intro assump_26
  intro assump_27
  intro assump_28
  apply And.intro
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_25
    case intro assump_39 assump_40 =>
      cases assump_40
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_44
          case inl assump_51 =>
            have assump_127 : p4 := by
              exact assump_30
            let assump_57 := assump_45 assump_127
            apply False.elim assump_57
          case inr assump_52 =>
            cases assump_52
            case inl assump_61 =>
              have assump_128 : p4 := by
                exact assump_30
              let assump_67 := assump_45 assump_128
              apply False.elim assump_67
            case inr assump_62 =>
              have assump_129 : p4 := by
                exact assump_30
              let assump_74 := assump_45 assump_129
              apply False.elim assump_74
  cases assump_28
  case intro assump_78 assump_79 =>
    cases assump_25
    case intro assump_88 assump_89 =>
      cases assump_89
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_93
          case inl assump_100 =>
            have assump_130 : p4 := by
              exact assump_79
            let assump_106 := assump_94 assump_130
            apply False.elim assump_106
          case inr assump_101 =>
            cases assump_101
            case inl assump_110 =>
              have assump_131 : p4 := by
                exact assump_79
              let assump_116 := assump_94 assump_131
              apply False.elim assump_116
            case inr assump_111 =>
              have assump_132 : p4 := by
                exact assump_79
              let assump_123 := assump_94 assump_132
              apply False.elim assump_123


variable (p0 p4 p7 p1 p3 p6 : Prop)
theorem file88_103965 : (((((p1 ∨ True) → False) → ((p1 ∨ False) ∨ (p3 ∧ p1))) → False) → ((((False → p7) ∧ (p6 ∧ p3)) → ((p6 → p0) → (p1 → False))) ∧ (((p4 ∨ p7) → (p4 → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_10
    case intro assump_13 assump_14 =>
      have assump_44 : (((p1 ∨ True) → False) → ((p1 ∨ False) ∨ (p3 ∧ p1))) := by
        intro assump_22
        apply Or.inl
        apply Or.inl
        exact assump_4
      let assump_21 := assump_1 assump_44
      apply False.elim assump_21
  intro assump_28
  have assump_45 : (((p1 ∨ True) → False) → ((p1 ∨ False) ∨ (p3 ∧ p1))) := by
    intro assump_34
    have assump_46 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_37 := assump_34 assump_46
    apply False.elim assump_37
  let assump_33 := assump_1 assump_45
  apply False.elim assump_33


variable (p1 p7 p4 p6 p3 p2 : Prop)
theorem file88_104975 : (((((p4 → True) → False) → ((p1 ∧ p6) → False)) ∨ (((p3 → p7) → False) ∨ ((p7 → p7) ∧ (False → False)))) ∨ ((((p3 ∨ False) ∧ (p7 → False)) → ((p4 ∧ p7) → (True ∨ True))) ∨ (((p6 ∨ p2) ∧ (p1 ∨ p4)) ∧ ((p6 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_16 : (p4 → True) := by
      intro assump_12
      apply True.intro
    let assump_11 := assump_1 assump_16
    apply False.elim assump_11


variable (p6 p0 p2 p1 p5 : Prop)
theorem file88_105530 : ((((((True ∨ p6) → False) → ((p5 ∧ p0) ∨ (True → p0))) → False) ∧ ((((p1 → p2) → (p6 → False)) ∨ ((p2 → False) ∧ (p2 ∨ p5))) ∧ (((True ∨ p2) ∨ (True → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_40 : ((True ∨ p2) ∨ (True → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_14 := assump_7 assump_40
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_18 assump_19 =>
          cases assump_19
          case inl assump_22 =>
            have assump_41 : ((True ∨ p2) ∨ (True → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_28 := assump_7 assump_41
            apply False.elim assump_28
          case inr assump_23 =>
            have assump_42 : ((True ∨ p2) ∨ (True → False)) := by
              apply Or.inl
              apply Or.inl
              apply True.intro
            let assump_36 := assump_7 assump_42
            apply False.elim assump_36


variable (p5 p3 : Prop)
theorem file88_106806 : (((((True → False) ∧ (False ∨ p3)) → ((p3 ∧ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_31 : (((True → False) ∧ (False ∨ p3)) → ((p3 ∧ p5) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          have assump_32 : True := by
            apply True.intro
          let assump_24 := assump_13 assump_32
          apply False.elim assump_24
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p0 p2 p6 p7 p5 p3 : Prop)
theorem file88_107537 : ((((((True ∨ p5) ∧ (False → p0)) → False) ∧ (((False ∨ True) ∨ (p7 → p5)) ∧ ((p3 → False) ∧ (p7 → p2)))) ∧ ((((p7 ∨ p0) ∧ (False → True)) → ((False ∧ p6) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              have assump_56 : (((p7 ∨ p0) ∧ (False → True)) → ((False ∧ p6) → False)) := by
                intro assump_27
                intro assump_28
                cases assump_28
                case intro assump_29 assump_30 =>
                  apply False.elim assump_29
              let assump_26 := assump_3 assump_56
              apply False.elim assump_26
        case inr assump_11 =>
          cases assump_9
          case intro assump_38 assump_39 =>
            have assump_57 : (((p7 ∨ p0) ∧ (False → True)) → ((False ∧ p6) → False)) := by
              intro assump_47
              intro assump_48
              cases assump_48
              case intro assump_49 assump_50 =>
                apply False.elim assump_49
            let assump_46 := assump_3 assump_57
            apply False.elim assump_46


variable (p4 p3 p6 p5 p2 : Prop)
theorem file88_109053 : (((((True ∧ p3) → False) ∧ ((True → False) ∨ (p4 → False))) ∧ (((True → False) ∧ (p6 ∨ p5)) ∧ ((p4 → False) ∧ (p2 → p3)))) → False) := by
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
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              cases assump_13
              case intro assump_22 assump_23 =>
                have assump_90 : True := by
                  apply True.intro
                let assump_31 := assump_14 assump_90
                apply False.elim assump_31
            case inr assump_19 =>
              cases assump_13
              case intro assump_37 assump_38 =>
                have assump_91 : True := by
                  apply True.intro
                let assump_46 := assump_14 assump_91
                apply False.elim assump_46
      case inr assump_9 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_55
            case inl assump_58 =>
              cases assump_53
              case intro assump_62 assump_63 =>
                have assump_92 : True := by
                  apply True.intro
                let assump_71 := assump_54 assump_92
                apply False.elim assump_71
            case inr assump_59 =>
              cases assump_53
              case intro assump_77 assump_78 =>
                have assump_93 : True := by
                  apply True.intro
                let assump_86 := assump_54 assump_93
                apply False.elim assump_86


variable (p0 p4 p1 p7 p2 : Prop)
theorem file88_110920 : ((((((p2 ∧ p7) → (False → False)) ∨ ((p1 ∧ p0) ∧ (p2 ∧ p2))) → (((p0 ∧ True) ∨ (p4 ∨ p0)) ∨ ((p0 ∧ p1) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p2 ∧ p7) → (False → False)) ∨ ((p1 ∧ p0) ∧ (p2 ∧ p2))) → (((p0 ∧ True) ∨ (p4 ∨ p0)) ∨ ((p0 ∧ p1) → (False → False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            apply Or.inl
            apply Or.inl
            apply And.intro
            exact assump_17
            apply True.intro
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p5 p3 p1 p4 p6 p0 p7 p2 : Prop)
theorem file88_111879 : (((((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) → (((False → False) → False) ∧ ((p5 ∧ p4) ∨ (p3 ∧ p7)))) → ((((p6 ∨ p7) ∨ (p3 → False)) ∧ ((p1 → False) → False)) ∧ (((p7 ∧ p3) ∨ (p0 → p1)) ∧ ((False → False) → (p7 ∧ False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inr
  intro assump_4
  have assump_73 : (((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_73
  let assump_9 := And.left assump_8
  have assump_74 : (False → False) := by
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_9 assump_74
  apply False.elim assump_10
  intro assump_17
  have assump_75 : (((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_22 := assump_1 assump_75
  let assump_23 := And.left assump_22
  have assump_76 : (False → False) := by
    intro assump_25
    apply False.elim assump_25
  let assump_24 := assump_23 assump_76
  apply False.elim assump_24
  apply And.intro
  apply Or.inr
  intro assump_33
  have assump_77 : (((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_37 := assump_1 assump_77
  let assump_38 := And.left assump_37
  have assump_78 : (False → False) := by
    intro assump_40
    apply False.elim assump_40
  let assump_39 := assump_38 assump_78
  apply False.elim assump_39
  intro assump_46
  apply And.intro
  have assump_79 : (((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_51 := assump_1 assump_79
  let assump_52 := And.left assump_51
  have assump_80 : (False → False) := by
    intro assump_54
    apply False.elim assump_54
  let assump_53 := assump_52 assump_80
  apply False.elim assump_53
  have assump_81 : (((True ∨ p0) ∨ (p1 → p2)) ∨ ((p1 → p2) ∧ (p3 → p6))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_64 := assump_1 assump_81
  let assump_65 := And.left assump_64
  have assump_82 : (False → False) := by
    intro assump_67
    apply False.elim assump_67
  let assump_66 := assump_65 assump_82
  apply False.elim assump_66


variable (p5 p0 p6 : Prop)
theorem file88_114292 : ((((((p5 → True) → False) → ((p0 → False) → (p5 ∨ p0))) ∨ (((True ∨ p5) ∧ (p0 → p6)) → False)) → False) → False) := by
  intro assump_5
  have assump_23 : ((((p5 → True) → False) → ((p0 → False) → (p5 ∨ p0))) ∨ (((True ∨ p5) ∧ (p0 → p6)) → False)) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    have assump_24 : (p5 → True) := by
      intro assump_16
      apply True.intro
    let assump_15 := assump_9 assump_24
    apply False.elim assump_15
  let assump_8 := assump_5 assump_23
  apply False.elim assump_8


variable (p2 p1 p0 p5 p4 p6 p7 : Prop)
theorem file88_114885 : ((((((p0 → False) ∧ (p2 → False)) → ((p0 → False) ∨ (p6 → p1))) ∨ (((p5 → p4) → False) → ((p7 ∨ True) → (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p0 → False) ∧ (p2 → False)) → ((p0 → False) ∨ (p6 → p1))) ∨ (((p5 → p4) → False) → ((p7 ∨ True) → (True ∨ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_25 : p0 := by
        exact assump_12
      let assump_17 := assump_6 assump_25
      apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p4 p2 p7 p0 p5 p6 : Prop)
theorem file88_115579 : (((((p4 ∧ p4) → False) ∨ ((p4 → p0) → False)) ∧ (((p6 → p2) → (p5 ∨ p7)) ∧ ((p5 ∨ True) → False))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_13
      case intro assump_18 assump_19 =>
        have assump_40 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_24 := assump_19 assump_40
        apply False.elim assump_24
    case inr assump_15 =>
      cases assump_13
      case intro assump_30 assump_31 =>
        have assump_41 : (p5 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_36 := assump_31 assump_41
        apply False.elim assump_36


variable (p6 p2 p3 p1 p0 p5 p7 p4 : Prop)
theorem file88_116373 : (((((p5 ∧ p3) → (p3 ∨ p2)) ∧ ((False ∧ p6) → (p5 → False))) → (((p1 ∨ True) → False) → ((p0 ∧ p6) → False))) ∨ ((((p3 → p1) → (p5 → p6)) ∧ ((p2 → p7) ∧ (p4 ∨ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      have assump_24 : (p1 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_20 := assump_2 assump_24
      apply False.elim assump_20


variable (p3 p6 p5 p4 p0 p7 p2 : Prop)
theorem file88_116952 : ((((((p0 → True) → False) → ((p5 → p7) ∨ (p6 → False))) → False) ∨ ((((True ∧ p4) ∨ (p4 → False)) → False) ∧ (((p6 → False) ∧ (p3 → p3)) ∨ ((p2 → p4) ∨ (p0 → p5))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_84 : (((p0 → True) → False) → ((p5 → p7) ∨ (p6 → False))) := by
      intro assump_7
      apply Or.inl
      intro assump_10
      have assump_85 : (p0 → True) := by
        intro assump_15
        apply True.intro
      let assump_14 := assump_7 assump_85
      apply False.elim assump_14
    let assump_6 := assump_2 assump_84
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_22 assump_23 =>
      cases assump_23
      case inl assump_26 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          have assump_86 : ((True ∧ p4) ∨ (p4 → False)) := by
            apply Or.inr
            intro assump_37
            have assump_87 : ((True ∧ p4) ∨ (p4 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              exact assump_37
            let assump_43 := assump_22 assump_87
            apply False.elim assump_43
          let assump_36 := assump_22 assump_86
          apply False.elim assump_36
      case inr assump_27 =>
        cases assump_27
        case inl assump_50 =>
          have assump_88 : ((True ∧ p4) ∨ (p4 → False)) := by
            apply Or.inr
            intro assump_56
            have assump_89 : ((True ∧ p4) ∨ (p4 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              exact assump_56
            let assump_61 := assump_22 assump_89
            apply False.elim assump_61
          let assump_55 := assump_22 assump_88
          apply False.elim assump_55
        case inr assump_51 =>
          have assump_90 : ((True ∧ p4) ∨ (p4 → False)) := by
            apply Or.inr
            intro assump_72
            have assump_91 : ((True ∧ p4) ∨ (p4 → False)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              exact assump_72
            let assump_77 := assump_22 assump_91
            apply False.elim assump_77
          let assump_71 := assump_22 assump_90
          apply False.elim assump_71


variable (p6 p3 p4 p2 p5 p1 : Prop)
theorem file88_119341 : (((((p1 → False) → False) ∧ ((p6 ∨ p3) → (p2 ∨ p2))) ∧ (((p5 → p6) → (p3 → False)) → False)) → ((((p2 ∧ p4) ∨ (False → False)) ∨ ((p4 → False) → False)) → (((True ∨ p6) ∧ (p6 ∨ True)) ∨ ((True ∧ p4) → (p5 ∧ p5))))) := by
  intro assump_15
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    cases assump_17
    case inl assump_19 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_15
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply Or.inl
            apply And.intro
            apply Or.inl
            apply True.intro
            apply Or.inr
            apply True.intro
    case inr assump_20 =>
      cases assump_15
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          apply Or.inl
          apply And.intro
          apply Or.inl
          apply True.intro
          apply Or.inr
          apply True.intro
  case inr assump_18 =>
    cases assump_15
    case intro assump_51 assump_52 =>
      cases assump_51
      case intro assump_53 assump_54 =>
        apply Or.inl
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inr
        apply True.intro


variable (p6 p7 p2 p0 p1 p3 p5 : Prop)
theorem file88_120692 : ((((((p2 ∨ p2) → (p7 → False)) ∧ ((p7 → False) ∨ (p5 → False))) → False) ∧ ((((True → p1) ∨ (p6 ∨ p0)) → ((False ∧ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((True → p1) ∨ (p6 ∨ p0)) → ((False ∧ p3) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p3 p6 p4 p7 p2 p5 p0 : Prop)
theorem file88_121266 : ((((((p5 ∨ True) → False) → ((p5 ∨ p2) ∨ (p6 ∧ p4))) → (((p6 → False) → (p5 ∨ p5)) ∧ ((p3 ∨ p4) ∨ (p5 ∧ True)))) ∧ ((((p3 → p0) → (p0 ∨ p6)) → False) ∧ (((p7 ∧ p0) ∧ (p6 ∧ p3)) ∧ ((True ∨ p7) → (p7 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              have assump_33 : (True ∨ p7) := by
                apply Or.inl
                apply True.intro
              let assump_28 := assump_11 assump_33
              have assump_34 : p7 := by
                exact assump_14
              let assump_29 := assump_28 assump_34
              apply False.elim assump_29


variable (p5 p6 p2 p7 p1 p3 : Prop)
theorem file88_122272 : ((((((p1 ∧ True) ∧ (p2 ∨ True)) ∧ ((p7 ∧ False) ∨ (p6 ∧ p7))) → (((p5 ∧ False) ∧ (p1 → p3)) → ((False → p2) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p1 ∧ True) ∧ (p2 ∨ True)) ∧ ((p7 ∧ False) ∨ (p6 ∧ p7))) → (((p5 ∧ False) ∧ (p1 → p3)) → ((False → p2) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p0 p2 : Prop)
theorem file88_122901 : ((((((p0 → p3) ∧ (False → False)) → False) → (((True ∨ p0) → False) ∧ ((p2 → False) → False))) ∧ ((((True ∨ True) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((True ∨ True) → False) → False) := by
      intro assump_9
      have assump_20 : (True ∨ True) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p2 p6 p4 p1 p7 p5 p0 : Prop)
theorem file88_123504 : (((((p7 ∨ p1) ∧ (p1 ∨ p7)) → ((p1 → True) ∧ (False ∨ True))) ∧ (((p1 ∨ p5) ∨ (p0 → p0)) ∧ ((p4 ∧ False) ∧ (False → False)))) → ((((p5 ∧ False) ∧ (p0 ∧ p1)) ∧ ((p1 → p1) → False)) ∨ (((p0 → p2) ∧ (p6 → p2)) → False))) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
        case inr assump_11 =>
          cases assump_7
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
      case inr assump_9 =>
        cases assump_7
        case intro assump_34 assump_35 =>
          cases assump_34
          case intro assump_36 assump_37 =>
            apply False.elim assump_37


variable (p7 p3 p2 p6 p1 p0 : Prop)
theorem file88_124610 : ((((((p0 → False) ∧ (p7 ∧ False)) ∧ ((p3 ∧ p0) → (p3 → True))) ∧ (((True → False) → False) → False)) ∧ ((((False ∨ p6) → (False ∨ p2)) ∧ ((p0 → p6) → (p6 → False))) ∨ (((True ∨ p2) → False) → ((True ∧ False) → (p1 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p1 p3 : Prop)
theorem file88_125250 : (((((p3 ∧ False) ∧ (p1 → p3)) → ((False ∧ False) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : (((p3 ∧ False) ∧ (p1 → p3)) → ((False ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p1 p4 p6 p3 p7 : Prop)
theorem file88_125682 : (((((False → False) ∧ (False → True)) → False) → False) ∨ ((((False ∧ p2) ∨ (p7 ∨ p3)) ∧ ((p4 → False) ∨ (False ∨ p7))) ∨ (((True → False) ∨ (p6 → p1)) ∨ ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((False → False) ∧ (False → True)) := by
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p6 p0 p7 p4 : Prop)
theorem file88_126191 : ((((((p6 ∧ False) ∨ (True → False)) → False) → False) ∧ ((((p6 ∧ p4) ∧ (False ∧ p7)) ∨ ((p6 ∨ p0) ∨ (p7 ∧ True))) ∧ (((p5 ∧ False) ∨ (p5 ∧ p0)) → ((p5 → False) → (False ∧ True))))) → False) := by
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_18
    case intro assump_21 assump_22 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_26
            case intro assump_33 assump_34 =>
              apply False.elim assump_33
      case inr assump_24 =>
        cases assump_24
        case inl assump_37 =>
          cases assump_37
          case inl assump_39 =>
            have assump_120 : (((p6 ∧ False) ∨ (True → False)) → False) := by
              intro assump_48
              cases assump_48
              case inl assump_49 =>
                cases assump_49
                case intro assump_51 assump_52 =>
                  apply False.elim assump_52
              case inr assump_50 =>
                have assump_121 : True := by
                  apply True.intro
                let assump_59 := assump_50 assump_121
                apply False.elim assump_59
            let assump_47 := assump_17 assump_120
            apply False.elim assump_47
          case inr assump_40 =>
            have assump_122 : (((p6 ∧ False) ∨ (True → False)) → False) := by
              intro assump_73
              cases assump_73
              case inl assump_74 =>
                cases assump_74
                case intro assump_76 assump_77 =>
                  apply False.elim assump_77
              case inr assump_75 =>
                have assump_123 : True := by
                  apply True.intro
                let assump_84 := assump_75 assump_123
                apply False.elim assump_84
            let assump_72 := assump_17 assump_122
            apply False.elim assump_72
        case inr assump_38 =>
          cases assump_38
          case intro assump_91 assump_92 =>
            have assump_124 : (((p6 ∧ False) ∨ (True → False)) → False) := by
              intro assump_102
              cases assump_102
              case inl assump_103 =>
                cases assump_103
                case intro assump_105 assump_106 =>
                  apply False.elim assump_106
              case inr assump_104 =>
                have assump_125 : True := by
                  apply True.intro
                let assump_113 := assump_104 assump_125
                apply False.elim assump_113
            let assump_101 := assump_17 assump_124
            apply False.elim assump_101


variable (p0 p2 p7 p1 p6 p4 p5 : Prop)
theorem file88_128975 : (((((p6 → False) → False) → False) ∧ (((p0 ∧ False) → (p5 ∧ p5)) → False)) → ((((p4 → False) → (p0 → p1)) ∨ ((p7 ∨ p7) ∨ (p6 ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      have assump_113 : ((p0 ∧ False) → (p5 ∧ p5)) := by
        intro assump_14
        apply And.intro
        cases assump_14
        case intro assump_15 assump_16 =>
          apply False.elim assump_16
        cases assump_14
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
      let assump_13 := assump_8 assump_113
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_30 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_1
        case intro assump_36 assump_37 =>
          have assump_114 : ((p0 ∧ False) → (p5 ∧ p5)) := by
            intro assump_43
            apply And.intro
            cases assump_43
            case intro assump_44 assump_45 =>
              apply False.elim assump_45
            cases assump_43
            case intro assump_50 assump_51 =>
              apply False.elim assump_51
          let assump_42 := assump_37 assump_114
          apply False.elim assump_42
      case inr assump_33 =>
        cases assump_1
        case intro assump_61 assump_62 =>
          have assump_115 : ((p0 ∧ False) → (p5 ∧ p5)) := by
            intro assump_68
            apply And.intro
            cases assump_68
            case intro assump_69 assump_70 =>
              apply False.elim assump_70
            cases assump_68
            case intro assump_75 assump_76 =>
              apply False.elim assump_76
          let assump_67 := assump_62 assump_115
          apply False.elim assump_67
    case inr assump_31 =>
      cases assump_31
      case intro assump_84 assump_85 =>
        cases assump_1
        case intro assump_90 assump_91 =>
          have assump_116 : ((p0 ∧ False) → (p5 ∧ p5)) := by
            intro assump_97
            apply And.intro
            cases assump_97
            case intro assump_98 assump_99 =>
              apply False.elim assump_99
            cases assump_97
            case intro assump_104 assump_105 =>
              apply False.elim assump_105
          let assump_96 := assump_91 assump_116
          apply False.elim assump_96


variable (p7 p0 p6 p2 p1 p5 p3 p4 : Prop)
theorem file88_131434 : ((((((p2 ∨ p0) ∧ (p4 → p1)) ∧ ((p6 ∨ p7) ∨ (False ∧ p3))) ∨ (((p3 ∨ p2) → False) → ((p7 → False) → (p2 → False)))) → ((((p0 → True) → False) ∧ ((p5 → False) ∨ (p2 → False))) ∧ (((p4 → p4) → False) ∨ ((p0 ∧ p5) ∨ (p7 → False))))) → False) := by
  intro assump_44
  have assump_68 : ((((p2 ∨ p0) ∧ (p4 → p1)) ∧ ((p6 ∨ p7) ∨ (False ∧ p3))) ∨ (((p3 ∨ p2) → False) → ((p7 → False) → (p2 → False)))) := by
    apply Or.inr
    intro assump_48
    intro assump_49
    intro assump_50
    have assump_69 : (p3 ∨ p2) := by
      apply Or.inr
      exact assump_50
    let assump_57 := assump_48 assump_69
    apply False.elim assump_57
  let assump_47 := assump_44 assump_68
  let assump_61 := And.left assump_47
  let assump_62 := And.left assump_61
  have assump_70 : (p0 → True) := by
    intro assump_64
    apply True.intro
  let assump_63 := assump_62 assump_70
  apply False.elim assump_63


variable (p5 p6 p0 p3 p4 p2 p1 : Prop)
theorem file88_132385 : (((((p6 → False) ∨ (p3 → False)) → ((p4 → False) ∧ (p0 → False))) ∧ (((p4 ∧ p5) → (p2 → False)) ∧ ((p1 ∧ False) ∧ (p5 ∧ p4)))) → ((((p0 ∧ p2) → False) ∧ ((p4 → p0) ∧ (False → False))) ∧ (((p5 → False) → False) ∧ ((False ∨ p5) ∨ (True ∨ p3))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
  apply And.intro
  intro assump_25
  cases assump_1
  case intro assump_28 assump_29 =>
    cases assump_29
    case intro assump_32 assump_33 =>
      cases assump_33
      case intro assump_36 assump_37 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          apply False.elim assump_39
  intro assump_44
  apply False.elim assump_44
  apply And.intro
  intro assump_47
  cases assump_1
  case intro assump_50 assump_51 =>
    cases assump_51
    case intro assump_54 assump_55 =>
      cases assump_55
      case intro assump_58 assump_59 =>
        cases assump_58
        case intro assump_60 assump_61 =>
          apply False.elim assump_61
  cases assump_1
  case intro assump_66 assump_67 =>
    cases assump_67
    case intro assump_70 assump_71 =>
      cases assump_71
      case intro assump_74 assump_75 =>
        cases assump_74
        case intro assump_76 assump_77 =>
          apply False.elim assump_77


variable (p1 p0 p2 p7 p3 p4 p6 : Prop)
theorem file88_134059 : ((((((p3 ∧ True) ∧ (p7 → p1)) ∨ ((p4 ∧ p2) ∧ (p3 → True))) → (((p2 ∧ p2) ∧ (p2 ∧ p6)) ∧ ((False → False) ∧ (False → False)))) ∧ ((((p7 → p3) → False) → ((False → p0) ∨ (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p7 → p3) → False) → ((False → p0) ∨ (p7 → True))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p5 p6 p4 p3 p1 p2 p0 : Prop)
theorem file88_134641 : (((((True → True) ∨ (p0 ∨ p4)) → False) → False) ∧ ((((p6 ∧ p3) ∨ (True ∧ True)) ∧ ((p0 → p1) → False)) → (((True → False) → (p5 ∨ True)) ∨ ((p5 ∨ p2) ∨ (p5 ∨ True))))) := by
  apply And.intro
  intro assump_20
  have assump_55 : ((True → True) ∨ (p0 ∨ p4)) := by
    apply Or.inl
    intro assump_24
    apply True.intro
  let assump_23 := assump_20 assump_55
  apply False.elim assump_23
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_29
    case inl assump_31 =>
      cases assump_31
      case intro assump_33 assump_34 =>
        apply Or.inl
        intro assump_41
        apply Or.inr
        apply True.intro
    case inr assump_32 =>
      cases assump_32
      case intro assump_44 assump_45 =>
        apply Or.inl
        intro assump_52
        apply Or.inr
        apply True.intro


variable (p6 p5 p4 p3 p7 : Prop)
theorem file88_135538 : ((((((p6 → p4) → False) → ((p5 ∧ p4) → False)) ∨ (((False ∨ p7) → False) ∧ ((True → p3) → False))) → False) → False) := by
  intro assump_5
  have assump_29 : ((((p6 → p4) → False) → ((p5 ∧ p4) → False)) ∨ (((False ∨ p7) → False) ∧ ((True → p3) → False))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      have assump_30 : (p6 → p4) := by
        intro assump_20
        exact assump_12
      let assump_19 := assump_9 assump_30
      apply False.elim assump_19
  let assump_8 := assump_5 assump_29
  apply False.elim assump_8


variable (p2 p3 p0 p4 p5 p6 : Prop)
theorem file88_136201 : ((((((p5 ∨ p3) → False) → False) → (((p4 ∧ True) ∧ (p2 ∧ p6)) ∧ ((p2 ∨ True) → False))) ∧ ((((False → False) ∧ (False → False)) ∨ ((False ∧ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((False → False) ∧ (False → False)) ∨ ((False ∧ p0) → False)) := by
      apply Or.inl
      apply And.intro
      intro assump_9
      apply False.elim assump_9
      intro assump_12
      apply False.elim assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p7 p6 p4 p5 p2 p1 p3 p0 : Prop)
theorem file88_136822 : ((((((p0 ∨ p0) → (p3 ∧ p3)) → ((p4 → False) → False)) → (((p1 → p5) → False) ∨ ((False ∨ p3) ∨ (p6 ∨ p2)))) ∧ ((((True ∨ p7) ∨ (p2 ∨ p5)) ∨ ((p2 ∨ p0) → (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((True ∨ p7) ∨ (p2 ∨ p5)) ∨ ((p2 ∨ p0) → (p7 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p5 p2 p3 p4 p1 p7 : Prop)
theorem file88_137376 : (((((p3 → p7) → (p1 ∨ p3)) → False) → False) → ((((False → p2) ∨ (p3 ∨ p4)) ∨ ((p5 → False) → False)) ∨ (((True → p1) ∨ (False → False)) ∨ ((p4 ∧ p2) ∧ (p3 → False))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_8
  apply False.elim assump_8


variable (p3 p1 p5 p4 p0 p7 : Prop)
theorem file88_137718 : ((((((True → False) → (p1 ∨ p0)) → False) ∧ (((p4 ∨ p7) ∨ (p7 ∨ p4)) → False)) ∧ ((((p1 ∨ p0) ∧ (p3 ∧ p5)) → False) ∨ (((True ∧ p5) ∨ (p4 ∧ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        have assump_42 : ((True → False) → (p1 ∨ p0)) := by
          intro assump_17
          have assump_43 : True := by
            apply True.intro
          let assump_20 := assump_17 assump_43
          apply False.elim assump_20
        let assump_16 := assump_4 assump_42
        apply False.elim assump_16
      case inr assump_11 =>
        have assump_44 : ((True → False) → (p1 ∨ p0)) := by
          intro assump_32
          have assump_45 : True := by
            apply True.intro
          let assump_35 := assump_32 assump_45
          apply False.elim assump_35
        let assump_31 := assump_4 assump_44
        apply False.elim assump_31


variable (p2 p0 p5 p6 p4 p7 : Prop)
theorem file88_138781 : (((((p0 → True) ∧ (p2 ∧ p7)) → ((True → p2) ∨ (p5 → False))) ∧ (((p6 ∨ True) → False) → False)) ∧ ((((p2 → p2) ∨ (p4 ∨ p2)) → False) → False)) := by
  apply And.intro
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      exact assump_6
  intro assump_15
  have assump_32 : (p6 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_18 := assump_15 assump_32
  apply False.elim assump_18
  intro assump_22
  have assump_33 : ((p2 → p2) ∨ (p4 ∨ p2)) := by
    apply Or.inl
    intro assump_26
    exact assump_26
  let assump_25 := assump_22 assump_33
  apply False.elim assump_25


variable (p3 p2 p4 p0 p5 p1 p6 p7 : Prop)
theorem file88_139570 : (((((p0 ∨ p7) ∧ (p6 ∨ p7)) ∨ ((True → False) → (p3 ∨ p1))) ∨ (((p2 → p7) → (p3 ∨ p0)) → ((True ∨ p4) ∧ (p2 → False)))) ∨ ((((p1 ∧ p0) → (p4 → p4)) → ((p0 ∧ p0) → False)) ∨ (((p0 → False) → False) ∧ ((p5 ∨ True) ∨ (p1 ∧ p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p6 p2 p3 p5 p1 p7 : Prop)
theorem file88_140042 : (((((False → False) ∨ (p1 ∨ p2)) → False) ∧ (((p3 → False) ∧ (p5 ∨ True)) ∧ ((True ∨ p5) → (p6 → False)))) → ((((p5 ∨ p1) → False) → ((p0 → False) → False)) ∧ (((p7 → False) → (True ∧ p1)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          have assump_93 : ((False → False) ∨ (p1 ∨ p2)) := by
            apply Or.inl
            intro assump_29
            apply False.elim assump_29
          let assump_28 := assump_8 assump_93
          apply False.elim assump_28
        case inr assump_19 =>
          have assump_94 : ((False → False) ∨ (p1 ∨ p2)) := by
            apply Or.inl
            intro assump_43
            apply False.elim assump_43
          let assump_42 := assump_8 assump_94
          apply False.elim assump_42
  intro assump_49
  cases assump_1
  case intro assump_52 assump_53 =>
    cases assump_53
    case intro assump_56 assump_57 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        cases assump_59
        case inl assump_62 =>
          have assump_95 : ((False → False) ∨ (p1 ∨ p2)) := by
            apply Or.inl
            intro assump_73
            apply False.elim assump_73
          let assump_72 := assump_52 assump_95
          apply False.elim assump_72
        case inr assump_63 =>
          have assump_96 : ((False → False) ∨ (p1 ∨ p2)) := by
            apply Or.inl
            intro assump_87
            apply False.elim assump_87
          let assump_86 := assump_52 assump_96
          apply False.elim assump_86


variable (p2 p4 p1 p6 p0 p3 p5 p7 : Prop)
theorem file88_141866 : ((((((True → p4) ∨ (p2 → p2)) ∨ ((p6 → p1) → (False → p7))) ∧ (((p5 → False) → False) ∧ ((p5 → p6) ∧ (p5 → p3)))) ∧ ((((True → False) ∧ (p5 → p5)) → ((p7 ∧ p5) → (p0 → False))) → False)) → False) := by
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
              have assump_133 : (((True → False) ∧ (p5 → p5)) → ((p7 ∧ p5) → (p0 → False))) := by
                intro assump_25
                intro assump_26
                intro assump_27
                cases assump_26
                case intro assump_30 assump_31 =>
                  cases assump_25
                  case intro assump_36 assump_37 =>
                    have assump_134 : True := by
                      apply True.intro
                    let assump_44 := assump_36 assump_134
                    apply False.elim assump_44
              let assump_24 := assump_3 assump_133
              apply False.elim assump_24
        case inr assump_9 =>
          cases assump_5
          case intro assump_53 assump_54 =>
            cases assump_54
            case intro assump_57 assump_58 =>
              have assump_135 : (((True → False) ∧ (p5 → p5)) → ((p7 ∧ p5) → (p0 → False))) := by
                intro assump_66
                intro assump_67
                intro assump_68
                cases assump_67
                case intro assump_71 assump_72 =>
                  cases assump_66
                  case intro assump_77 assump_78 =>
                    have assump_136 : True := by
                      apply True.intro
                    let assump_85 := assump_77 assump_136
                    apply False.elim assump_85
              let assump_65 := assump_3 assump_135
              apply False.elim assump_65
      case inr assump_7 =>
        cases assump_5
        case intro assump_94 assump_95 =>
          cases assump_95
          case intro assump_98 assump_99 =>
            have assump_137 : (((True → False) ∧ (p5 → p5)) → ((p7 ∧ p5) → (p0 → False))) := by
              intro assump_107
              intro assump_108
              intro assump_109
              cases assump_108
              case intro assump_112 assump_113 =>
                cases assump_107
                case intro assump_118 assump_119 =>
                  have assump_138 : True := by
                    apply True.intro
                  let assump_126 := assump_118 assump_138
                  apply False.elim assump_126
            let assump_106 := assump_3 assump_137
            apply False.elim assump_106


variable (p5 p7 p4 p3 p1 p6 : Prop)
theorem file88_144755 : ((((((p5 ∨ p4) ∨ (p3 ∧ p7)) ∨ ((p1 ∨ True) ∨ (p1 ∧ p3))) ∨ (((False ∨ p7) ∨ (True ∧ False)) ∨ ((True → p6) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p5 ∨ p4) ∨ (p3 ∧ p7)) ∨ ((p1 ∨ True) ∨ (p1 ∧ p3))) ∨ (((False ∨ p7) ∨ (True ∧ False)) ∨ ((True → p6) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p5 p1 p4 : Prop)
theorem file88_145261 : ((((((False → True) ∧ (True → False)) → ((True ∧ p7) ∨ (p5 → False))) ∨ (((False ∧ p5) → (p4 → False)) ∨ ((p5 ∧ True) → (p1 ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → True) ∧ (True → False)) → ((True ∧ p7) ∨ (p5 → False))) ∨ (((False ∧ p5) → (p4 → False)) ∨ ((p5 ∧ True) → (p1 ∧ True)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      intro assump_12
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_7 assump_24
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p6 p4 p0 p1 : Prop)
theorem file88_145983 : ((((((True ∧ False) → False) ∨ ((p4 ∨ p6) → (p0 ∨ True))) ∨ (((p2 → False) ∨ (p2 → True)) ∨ ((False → False) ∨ (p0 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∧ False) → False) ∨ ((p4 ∨ p6) → (p0 ∨ True))) ∨ (((p2 → False) ∨ (p2 → True)) ∨ ((False → False) ∨ (p0 ∨ p1)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p7 p3 p6 : Prop)
theorem file88_146554 : ((((((False ∧ p3) ∧ (p4 → p6)) → ((True ∨ p7) ∧ (p6 → True))) ∨ (((True → p6) → (False → True)) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p3) ∧ (p4 → p6)) → ((True ∨ p7) ∧ (p6 → True))) ∨ (((True → p6) → (False → True)) → False)) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    intro assump_12
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p4 p0 p1 p2 p5 : Prop)
theorem file88_147200 : (((((p1 ∧ p5) ∨ (p5 ∨ p2)) ∨ ((p2 → p2) → False)) ∧ (((False → False) → False) ∧ ((p0 ∨ p2) ∨ (p4 → False)))) → ((((p7 ∧ False) ∧ (p0 ∨ p4)) → ((True ∧ p5) → False)) ∧ (((True ∨ p4) → (p5 ∨ p2)) ∨ ((p1 → False) → False)))) := by
  intro assump_11
  apply And.intro
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_12
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  cases assump_11
  case intro assump_28 assump_29 =>
    cases assump_28
    case inl assump_30 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          cases assump_29
          case intro assump_40 assump_41 =>
            cases assump_41
            case inl assump_44 =>
              cases assump_44
              case inl assump_46 =>
                apply Or.inl
                intro assump_50
                cases assump_50
                case inl assump_51 =>
                  apply Or.inl
                  exact assump_35
                case inr assump_52 =>
                  apply Or.inl
                  exact assump_35
              case inr assump_47 =>
                apply Or.inl
                intro assump_59
                cases assump_59
                case inl assump_60 =>
                  apply Or.inl
                  exact assump_35
                case inr assump_61 =>
                  apply Or.inl
                  exact assump_35
            case inr assump_45 =>
              apply Or.inl
              intro assump_68
              cases assump_68
              case inl assump_69 =>
                apply Or.inl
                exact assump_35
              case inr assump_70 =>
                apply Or.inl
                exact assump_35
      case inr assump_33 =>
        cases assump_33
        case inl assump_75 =>
          cases assump_29
          case intro assump_79 assump_80 =>
            cases assump_80
            case inl assump_83 =>
              cases assump_83
              case inl assump_85 =>
                apply Or.inl
                intro assump_89
                cases assump_89
                case inl assump_90 =>
                  apply Or.inl
                  exact assump_75
                case inr assump_91 =>
                  apply Or.inl
                  exact assump_75
              case inr assump_86 =>
                apply Or.inl
                intro assump_98
                cases assump_98
                case inl assump_99 =>
                  apply Or.inl
                  exact assump_75
                case inr assump_100 =>
                  apply Or.inl
                  exact assump_75
            case inr assump_84 =>
              apply Or.inl
              intro assump_107
              cases assump_107
              case inl assump_108 =>
                apply Or.inl
                exact assump_75
              case inr assump_109 =>
                apply Or.inl
                exact assump_75
        case inr assump_76 =>
          cases assump_29
          case intro assump_116 assump_117 =>
            cases assump_117
            case inl assump_120 =>
              cases assump_120
              case inl assump_122 =>
                apply Or.inl
                intro assump_126
                cases assump_126
                case inl assump_127 =>
                  apply Or.inr
                  exact assump_76
                case inr assump_128 =>
                  apply Or.inr
                  exact assump_76
              case inr assump_123 =>
                apply Or.inl
                intro assump_135
                cases assump_135
                case inl assump_136 =>
                  apply Or.inr
                  exact assump_123
                case inr assump_137 =>
                  apply Or.inr
                  exact assump_123
            case inr assump_121 =>
              apply Or.inl
              intro assump_144
              cases assump_144
              case inl assump_145 =>
                apply Or.inr
                exact assump_76
              case inr assump_146 =>
                apply Or.inr
                exact assump_76
    case inr assump_31 =>
      cases assump_29
      case intro assump_153 assump_154 =>
        cases assump_154
        case inl assump_157 =>
          cases assump_157
          case inl assump_159 =>
            apply Or.inl
            intro assump_163
            cases assump_163
            case inl assump_164 =>
              have assump_218 : (False → False) := by
                intro assump_170
                apply False.elim assump_170
              let assump_169 := assump_153 assump_218
              apply False.elim assump_169
            case inr assump_165 =>
              have assump_219 : (False → False) := by
                intro assump_181
                apply False.elim assump_181
              let assump_180 := assump_153 assump_219
              apply False.elim assump_180
          case inr assump_160 =>
            apply Or.inl
            intro assump_189
            cases assump_189
            case inl assump_190 =>
              apply Or.inr
              exact assump_160
            case inr assump_191 =>
              apply Or.inr
              exact assump_160
        case inr assump_158 =>
          apply Or.inl
          intro assump_198
          cases assump_198
          case inl assump_199 =>
            have assump_220 : (False → False) := by
              intro assump_205
              apply False.elim assump_205
            let assump_204 := assump_153 assump_220
            apply False.elim assump_204
          case inr assump_200 =>
            have assump_221 : p4 := by
              exact assump_200
            let assump_214 := assump_158 assump_221
            apply False.elim assump_214


variable (p1 p6 p0 p5 p4 p2 p7 p3 : Prop)
theorem file88_153240 : ((((((p4 → False) → (p2 → p2)) ∨ ((p3 ∨ p6) ∧ (True ∨ p1))) ∨ (((p7 ∧ p5) ∧ (p1 ∧ p0)) ∨ ((p0 ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 → False) → (p2 → p2)) ∨ ((p3 ∨ p6) ∧ (True ∨ p1))) ∨ (((p7 ∧ p5) ∧ (p1 ∧ p0)) ∨ ((p0 ∧ p1) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    exact assump_6
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p3 p7 p2 p1 p0 p5 : Prop)
theorem file88_153745 : (((((p5 → p0) ∨ (p1 ∨ p6)) → ((False → p2) → False)) → (((True ∨ p6) ∧ (p1 → False)) → ((p0 → False) ∨ (True ∧ p3)))) ∨ ((((p7 → False) → False) → False) ∨ (((False ∧ p3) → False) → False))) := by
  apply Or.inl
  intro assump_10
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      apply Or.inl
      intro assump_22
      have assump_58 : ((p5 → p0) ∨ (p1 ∨ p6)) := by
        apply Or.inl
        intro assump_27
        exact assump_22
      let assump_26 := assump_10 assump_58
      have assump_59 : (False → p2) := by
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_26 assump_59
      apply False.elim assump_30
    case inr assump_15 =>
      apply Or.inl
      intro assump_43
      have assump_60 : ((p5 → p0) ∨ (p1 ∨ p6)) := by
        apply Or.inl
        intro assump_48
        exact assump_43
      let assump_47 := assump_10 assump_60
      have assump_61 : (False → p2) := by
        intro assump_52
        apply False.elim assump_52
      let assump_51 := assump_47 assump_61
      apply False.elim assump_51


variable (p4 p2 p3 p6 p5 : Prop)
theorem file88_154942 : (((((p3 → False) ∧ (p2 ∨ p4)) → ((p3 → False) ∨ (p2 ∨ p5))) → False) → ((((p4 ∨ p2) ∧ (p6 → p6)) → False) ∧ (((p5 ∨ True) ∧ (True → False)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_168 : (((p3 → False) ∧ (p2 ∨ p4)) → ((p3 → False) ∨ (p2 ∨ p5))) := by
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          cases assump_16
          case inl assump_19 =>
            apply Or.inl
            intro assump_23
            have assump_169 : p3 := by
              exact assump_23
            let assump_28 := assump_15 assump_169
            apply False.elim assump_28
          case inr assump_20 =>
            apply Or.inl
            intro assump_34
            have assump_170 : p3 := by
              exact assump_34
            let assump_39 := assump_15 assump_170
            apply False.elim assump_39
      let assump_13 := assump_1 assump_168
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_171 : (((p3 → False) ∧ (p2 ∨ p4)) → ((p3 → False) ∨ (p2 ∨ p5))) := by
        intro assump_53
        cases assump_53
        case intro assump_54 assump_55 =>
          cases assump_55
          case inl assump_58 =>
            apply Or.inl
            intro assump_62
            have assump_172 : p3 := by
              exact assump_62
            let assump_67 := assump_54 assump_172
            apply False.elim assump_67
          case inr assump_59 =>
            apply Or.inl
            intro assump_73
            have assump_173 : p3 := by
              exact assump_73
            let assump_78 := assump_54 assump_173
            apply False.elim assump_78
      let assump_52 := assump_1 assump_171
      apply False.elim assump_52
  intro assump_85
  cases assump_85
  case intro assump_86 assump_87 =>
    cases assump_86
    case inl assump_88 =>
      have assump_174 : (((p3 → False) ∧ (p2 ∨ p4)) → ((p3 → False) ∨ (p2 ∨ p5))) := by
        intro assump_97
        cases assump_97
        case intro assump_98 assump_99 =>
          cases assump_99
          case inl assump_102 =>
            apply Or.inl
            intro assump_106
            have assump_175 : p3 := by
              exact assump_106
            let assump_111 := assump_98 assump_175
            apply False.elim assump_111
          case inr assump_103 =>
            apply Or.inl
            intro assump_117
            have assump_176 : p3 := by
              exact assump_117
            let assump_122 := assump_98 assump_176
            apply False.elim assump_122
      let assump_96 := assump_1 assump_174
      apply False.elim assump_96
    case inr assump_89 =>
      have assump_177 : (((p3 → False) ∧ (p2 ∨ p4)) → ((p3 → False) ∨ (p2 ∨ p5))) := by
        intro assump_136
        cases assump_136
        case intro assump_137 assump_138 =>
          cases assump_138
          case inl assump_141 =>
            apply Or.inl
            intro assump_145
            have assump_178 : p3 := by
              exact assump_145
            let assump_150 := assump_137 assump_178
            apply False.elim assump_150
          case inr assump_142 =>
            apply Or.inl
            intro assump_156
            have assump_179 : p3 := by
              exact assump_156
            let assump_161 := assump_137 assump_179
            apply False.elim assump_161
      let assump_135 := assump_1 assump_177
      apply False.elim assump_135


variable (p7 p3 p0 p1 : Prop)
theorem file88_158562 : ((((((True → False) → False) → False) → (((True ∧ p7) → (p3 ∧ False)) → ((p1 ∨ p7) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_50 : ((((True → False) → False) → False) → (((True ∧ p7) → (p3 ∧ False)) → ((p1 ∨ p7) → (p0 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      have assump_51 : ((True → False) → False) := by
        intro assump_20
        have assump_52 : True := by
          apply True.intro
        let assump_23 := assump_20 assump_52
        apply False.elim assump_23
      let assump_19 := assump_5 assump_51
      apply False.elim assump_19
    case inr assump_12 =>
      have assump_53 : ((True → False) → False) := by
        intro assump_37
        have assump_54 : True := by
          apply True.intro
        let assump_40 := assump_37 assump_54
        apply False.elim assump_40
      let assump_36 := assump_5 assump_53
      apply False.elim assump_36
  let assump_4 := assump_1 assump_50
  apply False.elim assump_4


variable (p5 p6 p3 p1 p4 p2 : Prop)
theorem file88_159692 : ((((((p5 ∧ p3) → (False ∨ p5)) → False) → (((p6 → False) → (p1 → False)) → ((p4 → p6) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p5 ∧ p3) → (False ∨ p5)) → False) → (((p6 → False) → (p1 → False)) → ((p4 → p6) ∧ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    have assump_47 : ((p5 ∧ p3) → (False ∨ p5)) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply Or.inr
        exact assump_16
    let assump_14 := assump_5 assump_47
    apply False.elim assump_14
    intro assump_25
    have assump_48 : ((p5 ∧ p3) → (False ∨ p5)) := by
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        apply Or.inr
        exact assump_34
    let assump_32 := assump_5 assump_48
    apply False.elim assump_32
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p5 p2 p4 p7 p0 p1 : Prop)
theorem file88_160694 : ((((((p0 ∨ p5) ∨ (p0 → p2)) → False) → (((p4 → False) → False) → ((p1 ∨ p5) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p0 ∨ p5) ∨ (p0 → p2)) → False) → (((p4 → False) → False) → ((p1 ∨ p5) → (p7 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case inl assump_11 =>
      have assump_45 : ((p0 ∨ p5) ∨ (p0 → p2)) := by
        apply Or.inr
        intro assump_20
        have assump_46 : ((p0 ∨ p5) ∨ (p0 → p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_20
        let assump_24 := assump_5 assump_46
        apply False.elim assump_24
      let assump_19 := assump_5 assump_45
      apply False.elim assump_19
    case inr assump_12 =>
      have assump_47 : ((p0 ∨ p5) ∨ (p0 → p2)) := by
        apply Or.inl
        apply Or.inr
        exact assump_12
      let assump_37 := assump_5 assump_47
      apply False.elim assump_37
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


