variable (p0 p1 p4 p5 p2 : Prop)
theorem file33_41 : (((((p0 → False) → False) ∧ ((p4 → False) ∨ (p4 ∧ False))) ∧ (((p5 → p5) → (p1 ∨ True)) → False)) → ((((p2 ∨ True) → False) ∨ ((p0 → False) → False)) ∧ (((p5 ∨ p2) → False) ∧ ((p4 → False) ∧ (p1 ∨ p5))))) := by
  intro assump_16
  apply And.intro
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case inl assump_23 =>
        apply Or.inl
        intro assump_29
        cases assump_29
        case inl assump_30 =>
          have assump_167 : ((p5 → p5) → (p1 ∨ True)) := by
            intro assump_36
            apply Or.inr
            apply True.intro
          let assump_35 := assump_18 assump_167
          apply False.elim assump_35
        case inr assump_31 =>
          have assump_168 : ((p5 → p5) → (p1 ∨ True)) := by
            intro assump_45
            apply Or.inr
            apply True.intro
          let assump_44 := assump_18 assump_168
          apply False.elim assump_44
      case inr assump_24 =>
        cases assump_24
        case intro assump_51 assump_52 =>
          apply False.elim assump_52
  apply And.intro
  intro assump_57
  cases assump_57
  case inl assump_58 =>
    cases assump_16
    case intro assump_62 assump_63 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        cases assump_65
        case inl assump_68 =>
          have assump_169 : ((p5 → p5) → (p1 ∨ True)) := by
            intro assump_75
            apply Or.inr
            apply True.intro
          let assump_74 := assump_63 assump_169
          apply False.elim assump_74
        case inr assump_69 =>
          cases assump_69
          case intro assump_81 assump_82 =>
            apply False.elim assump_82
  case inr assump_59 =>
    cases assump_16
    case intro assump_89 assump_90 =>
      cases assump_89
      case intro assump_91 assump_92 =>
        cases assump_92
        case inl assump_95 =>
          have assump_170 : ((p5 → p5) → (p1 ∨ True)) := by
            intro assump_102
            apply Or.inr
            apply True.intro
          let assump_101 := assump_90 assump_170
          apply False.elim assump_101
        case inr assump_96 =>
          cases assump_96
          case intro assump_108 assump_109 =>
            apply False.elim assump_109
  apply And.intro
  intro assump_114
  cases assump_16
  case intro assump_117 assump_118 =>
    cases assump_117
    case intro assump_119 assump_120 =>
      cases assump_120
      case inl assump_123 =>
        have assump_171 : ((p5 → p5) → (p1 ∨ True)) := by
          intro assump_130
          apply Or.inr
          apply True.intro
        let assump_129 := assump_118 assump_171
        apply False.elim assump_129
      case inr assump_124 =>
        cases assump_124
        case intro assump_136 assump_137 =>
          apply False.elim assump_137
  cases assump_16
  case intro assump_142 assump_143 =>
    cases assump_142
    case intro assump_144 assump_145 =>
      cases assump_145
      case inl assump_148 =>
        have assump_172 : ((p5 → p5) → (p1 ∨ True)) := by
          intro assump_155
          apply Or.inr
          apply True.intro
        let assump_154 := assump_143 assump_172
        apply False.elim assump_154
      case inr assump_149 =>
        cases assump_149
        case intro assump_161 assump_162 =>
          apply False.elim assump_162


variable (p4 p3 p5 p1 p0 p6 : Prop)
theorem file33_3497 : ((((((p4 → p3) → (p6 → False)) ∧ ((p4 ∨ p0) → (p1 → False))) → (((p5 → p5) ∨ (True → False)) ∨ ((p6 ∧ p3) ∧ (True ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 → p3) → (p6 → False)) ∧ ((p4 ∨ p0) → (p1 → False))) → (((p5 → p5) ∨ (True → False)) ∨ ((p6 ∧ p3) ∧ (True ∧ p3)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_12
      exact assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p4 : Prop)
theorem file33_4076 : ((((((p3 ∨ p3) → False) ∧ ((p3 → False) ∧ (False ∧ p4))) → False) → False) → False) := by
  intro assump_5
  have assump_25 : ((((p3 ∨ p3) → False) ∧ ((p3 → False) ∧ (False ∧ p4))) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_8 := assump_5 assump_25
  apply False.elim assump_8


variable (p3 p5 p7 p0 p2 p1 p6 : Prop)
theorem file33_4641 : (((((False ∧ p2) → (p1 → False)) → False) → False) ∨ ((((True ∧ p3) → False) ∨ ((p7 → False) → False)) ∨ (((p2 ∨ p2) ∧ (p6 ∨ p5)) → ((p5 ∨ p3) ∨ (p7 → p0))))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((False ∧ p2) → (p1 → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p1 p4 p2 p7 p5 : Prop)
theorem file33_5144 : (((((p5 ∨ True) ∨ (p4 ∧ False)) ∨ ((True → p6) ∧ (p1 ∧ p7))) → False) → ((((p2 ∧ True) ∧ (p7 → False)) → ((p4 → p5) → (p5 → False))) ∨ (((True ∨ p2) ∧ (p7 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      have assump_29 : (((p5 ∨ True) ∨ (p4 ∧ False)) ∨ ((True → p6) ∧ (p1 ∧ p7))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_6
      let assump_25 := assump_1 assump_29
      apply False.elim assump_25


variable (p7 p3 p5 p0 p2 p4 : Prop)
theorem file33_5829 : (((((p5 → p5) ∨ (p7 ∨ p7)) → False) ∨ (((p3 ∨ p3) ∧ (p2 ∧ p4)) ∧ ((p0 → p0) ∧ (False ∧ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_51 : ((p5 → p5) ∨ (p7 ∨ p7)) := by
      apply Or.inl
      intro assump_7
      exact assump_7
    let assump_6 := assump_2 assump_51
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          cases assump_16
          case intro assump_21 assump_22 =>
            cases assump_14
            case intro assump_27 assump_28 =>
              cases assump_28
              case intro assump_31 assump_32 =>
                apply False.elim assump_31
        case inr assump_18 =>
          cases assump_16
          case intro assump_37 assump_38 =>
            cases assump_14
            case intro assump_43 assump_44 =>
              cases assump_44
              case intro assump_47 assump_48 =>
                apply False.elim assump_47


variable (p4 p7 p1 p3 p0 p6 : Prop)
theorem file33_6992 : ((((((False → False) → (p3 ∧ True)) ∨ ((False → p7) ∨ (p7 → False))) → (((p1 → p6) ∨ (p7 ∧ p4)) → False)) ∧ ((((p1 ∨ True) ∨ (p7 ∨ False)) ∨ ((False ∨ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p1 ∨ True) ∨ (p7 ∨ False)) ∨ ((False ∨ p0) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p1 p2 p7 p6 : Prop)
theorem file33_7536 : ((((((p6 → p6) ∨ (True ∧ p7)) → False) → (((False → p7) ∨ (p1 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p6 → p6) ∨ (True ∧ p7)) → False) → (((False → p7) ∨ (p1 ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_39 : ((p6 → p6) ∨ (True ∧ p7)) := by
        apply Or.inl
        intro assump_14
        exact assump_14
      let assump_13 := assump_5 assump_39
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_20 assump_21 =>
        have assump_40 : ((p6 → p6) ∨ (True ∧ p7)) := by
          apply Or.inl
          intro assump_29
          exact assump_29
        let assump_28 := assump_5 assump_40
        apply False.elim assump_28
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p3 p1 p2 p5 : Prop)
theorem file33_8455 : ((((((p3 → False) → False) → ((p5 ∨ p2) → (p3 ∨ True))) ∨ (((p1 ∨ p2) → False) → False)) → False) → False) := by
  intro assump_5
  have assump_24 : ((((p3 → False) → False) → ((p5 ∨ p2) → (p3 ∨ True))) ∨ (((p1 ∨ p2) → False) → False)) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case inl assump_11 =>
      apply Or.inr
      apply True.intro
    case inr assump_12 =>
      apply Or.inr
      apply True.intro
  let assump_8 := assump_5 assump_24
  apply False.elim assump_8


variable (p6 p5 p1 p7 p4 p2 p0 : Prop)
theorem file33_9037 : (((((p2 → p1) ∨ (p7 → p5)) → ((p5 → False) ∧ (p6 → False))) → (((p4 ∨ p4) ∧ (p4 ∧ p2)) ∧ ((p0 → False) ∨ (p6 → False)))) → ((((True → False) → (p7 ∨ p1)) → False) → (((True ∧ True) ∨ (p2 → p6)) ∨ ((p6 ∨ p1) → (p6 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p0 p7 p5 p3 : Prop)
theorem file33_9440 : ((((((True → False) → False) ∧ ((p7 → False) → (False → p5))) ∨ (((True ∨ False) ∨ (p0 ∨ p0)) ∧ ((p3 → False) ∨ (p0 → False)))) → False) → False) := by
  intro assump_21
  have assump_39 : ((((True → False) → False) ∧ ((p7 → False) → (False → p5))) ∨ (((True ∨ False) ∨ (p0 ∨ p0)) ∧ ((p3 → False) ∨ (p0 → False)))) := by
    apply Or.inl
    apply And.intro
    intro assump_25
    have assump_40 : True := by
      apply True.intro
    let assump_28 := assump_25 assump_40
    apply False.elim assump_28
    intro assump_32
    intro assump_33
    apply False.elim assump_33
  let assump_24 := assump_21 assump_39
  apply False.elim assump_24


variable (p5 p2 p3 p7 p1 p0 : Prop)
theorem file33_10144 : ((((((True ∧ p0) ∨ (p5 → p0)) → False) → False) ∧ ((((p3 ∧ False) ∧ (p5 → p5)) ∧ ((p2 ∧ p1) ∧ (p1 ∧ False))) ∧ (((True ∨ p0) → (p7 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13


variable (p3 p1 p0 p6 p4 p5 : Prop)
theorem file33_10724 : (((((False ∧ p5) ∨ (p1 → False)) → False) ∧ (((p0 ∧ p1) → (p1 → False)) ∨ ((True ∧ p0) → False))) → ((((True ∧ p4) → (False ∧ True)) → ((p5 ∨ p1) → False)) → (((p1 ∨ False) → (p0 → p3)) ∨ ((p0 → p6) → False)))) := by
  intro assump_20
  intro assump_21
  cases assump_20
  case intro assump_24 assump_25 =>
    cases assump_25
    case inl assump_28 =>
      apply Or.inl
      intro assump_32
      intro assump_33
      cases assump_32
      case inl assump_36 =>
        have assump_67 : (p0 ∧ p1) := by
          apply And.intro
          exact assump_33
          exact assump_36
        let assump_42 := assump_28 assump_67
        have assump_68 : p1 := by
          exact assump_36
        let assump_43 := assump_42 assump_68
        apply False.elim assump_43
      case inr assump_37 =>
        apply False.elim assump_37
    case inr assump_29 =>
      apply Or.inl
      intro assump_51
      intro assump_52
      cases assump_51
      case inl assump_55 =>
        have assump_69 : (True ∧ p0) := by
          apply And.intro
          apply True.intro
          exact assump_52
        let assump_61 := assump_29 assump_69
        apply False.elim assump_61
      case inr assump_56 =>
        apply False.elim assump_56


variable (p1 p5 p4 p7 p6 : Prop)
theorem file33_12018 : ((((((p6 ∨ p1) ∧ (False ∧ p6)) → False) ∨ (((p7 ∧ p5) → False) → False)) → ((((p6 ∧ True) ∨ (p6 → False)) ∨ ((p4 → p6) ∨ (p1 ∧ p5))) → False)) → False) := by
  intro assump_1
  have assump_52 : ((((p6 ∨ p1) ∧ (False ∧ p6)) → False) ∨ (((p7 ∧ p5) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_9 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_4 := assump_1 assump_52
  have assump_53 : (((p6 ∧ True) ∨ (p6 → False)) ∨ ((p4 → p6) ∨ (p1 ∧ p5))) := by
    apply Or.inl
    apply Or.inr
    intro assump_23
    have assump_54 : ((((p6 ∨ p1) ∧ (False ∧ p6)) → False) ∨ (((p7 ∧ p5) → False) → False)) := by
      apply Or.inl
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        cases assump_29
        case inl assump_31 =>
          cases assump_30
          case intro assump_35 assump_36 =>
            apply False.elim assump_35
        case inr assump_32 =>
          cases assump_30
          case intro assump_41 assump_42 =>
            apply False.elim assump_41
    let assump_27 := assump_1 assump_54
    have assump_55 : (((p6 ∧ True) ∨ (p6 → False)) ∨ ((p4 → p6) ∨ (p1 ∧ p5))) := by
      apply Or.inl
      apply Or.inl
      apply And.intro
      exact assump_23
      apply True.intro
    let assump_45 := assump_27 assump_55
    apply False.elim assump_45
  let assump_22 := assump_4 assump_53
  apply False.elim assump_22


variable (p3 p6 p5 : Prop)
theorem file33_13754 : (((((p3 ∨ True) → False) ∨ ((True → False) → (p5 → False))) ∧ (((p6 → False) → (True ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : ((p6 → False) → (True ∨ True)) := by
        intro assump_11
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : ((p6 → False) → (True ∨ True)) := by
        intro assump_22
        apply Or.inl
        apply True.intro
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p6 p2 p7 p1 p0 p4 : Prop)
theorem file33_14480 : (((((p6 ∧ False) ∧ (p0 → False)) → ((p7 ∧ p4) → (True → False))) ∨ (((True ∨ p1) → False) ∧ ((True → True) → False))) ∨ ((((p6 → False) ∨ (p4 ∧ p6)) ∧ ((False ∨ p7) ∨ (False → False))) ∧ (((True → p4) → (p4 → False)) ∧ ((p4 ∨ p0) ∨ (p2 ∧ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_15


variable (p7 p6 p0 p1 p3 p4 p5 p2 : Prop)
theorem file33_15084 : (((((p2 → p6) → (p1 → p3)) → False) → (((p0 ∨ p0) ∨ (False → False)) → ((p3 → p5) ∨ (True ∨ p7)))) ∨ ((((p5 ∨ p2) ∧ (p2 ∨ p2)) → ((False ∨ p0) → (p1 → p2))) → (((p4 ∨ p0) ∧ (p5 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      intro assump_11
      have assump_61 : ((p2 → p6) → (p1 → p3)) := by
        intro assump_16
        intro assump_17
        exact assump_11
      let assump_15 := assump_1 assump_61
      apply False.elim assump_15
    case inr assump_6 =>
      apply Or.inl
      intro assump_29
      have assump_62 : ((p2 → p6) → (p1 → p3)) := by
        intro assump_34
        intro assump_35
        exact assump_29
      let assump_33 := assump_1 assump_62
      apply False.elim assump_33
  case inr assump_4 =>
    apply Or.inl
    intro assump_47
    have assump_63 : ((p2 → p6) → (p1 → p3)) := by
      intro assump_52
      intro assump_53
      exact assump_47
    let assump_51 := assump_1 assump_63
    apply False.elim assump_51


variable (p4 p0 p5 p7 p6 p3 : Prop)
theorem file33_16233 : (((((p7 ∨ p3) → (True → True)) ∨ ((p4 → False) → False)) ∨ (((p4 → False) ∨ (p6 ∨ p5)) ∨ ((p3 → False) → False))) ∨ ((((True ∨ p4) ∧ (p3 → False)) → False) ∧ (((p6 ∧ p0) ∨ (p5 ∧ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro


variable (p0 p5 p4 p6 p1 p2 p3 : Prop)
theorem file33_16594 : (((((True ∨ p6) → False) ∧ ((p0 ∧ p4) ∨ (p5 → False))) → (((p0 ∨ p5) → (p3 ∨ p6)) ∧ ((p0 ∧ p1) ∧ (p2 ∧ p1)))) ∨ ((((p6 ∧ p3) → (p2 ∧ p1)) → False) → (((True → False) ∨ (p1 ∨ p2)) → ((p1 → False) ∨ (True ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_152 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_21 := assump_7 assump_152
          apply False.elim assump_21
      case inr assump_12 =>
        have assump_153 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_28 := assump_7 assump_153
        apply False.elim assump_28
  case inr assump_4 =>
    cases assump_1
    case intro assump_34 assump_35 =>
      cases assump_35
      case inl assump_38 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          have assump_154 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_48 := assump_34 assump_154
          apply False.elim assump_48
      case inr assump_39 =>
        have assump_155 : p5 := by
          exact assump_4
        let assump_54 := assump_39 assump_155
        apply False.elim assump_54
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_58 assump_59 =>
    cases assump_59
    case inl assump_62 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        exact assump_64
    case inr assump_63 =>
      have assump_156 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_73 := assump_58 assump_156
      apply False.elim assump_73
  cases assump_1
  case intro assump_77 assump_78 =>
    cases assump_78
    case inl assump_81 =>
      cases assump_81
      case intro assump_83 assump_84 =>
        have assump_157 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_91 := assump_77 assump_157
        apply False.elim assump_91
    case inr assump_82 =>
      have assump_158 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_98 := assump_77 assump_158
      apply False.elim assump_98
  apply And.intro
  cases assump_1
  case intro assump_102 assump_103 =>
    cases assump_103
    case inl assump_106 =>
      cases assump_106
      case intro assump_108 assump_109 =>
        have assump_159 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_116 := assump_102 assump_159
        apply False.elim assump_116
    case inr assump_107 =>
      have assump_160 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_123 := assump_102 assump_160
      apply False.elim assump_123
  cases assump_1
  case intro assump_127 assump_128 =>
    cases assump_128
    case inl assump_131 =>
      cases assump_131
      case intro assump_133 assump_134 =>
        have assump_161 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_141 := assump_127 assump_161
        apply False.elim assump_141
    case inr assump_132 =>
      have assump_162 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_148 := assump_127 assump_162
      apply False.elim assump_148


variable (p6 p0 p2 p1 : Prop)
theorem file33_20119 : ((((((p1 → False) ∧ (p1 ∧ p2)) ∧ ((p1 → p1) → False)) → (((True → p1) → False) ∨ ((p6 ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p1 → False) ∧ (p1 ∧ p2)) ∧ ((p1 → p1) → False)) → (((True → p1) → False) ∨ ((p6 ∨ p0) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          have assump_36 : (p1 → p1) := by
            intro assump_26
            exact assump_26
          let assump_25 := assump_7 assump_36
          apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p5 p7 p1 : Prop)
theorem file33_20934 : ((((((False → True) ∨ (p1 → False)) → ((p5 → False) ∨ (p7 → False))) → False) ∧ ((((p5 ∧ True) ∧ (False ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p5 ∧ True) ∧ (False ∧ False)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p4 p7 p5 p3 p2 p1 : Prop)
theorem file33_21605 : (((((p2 → False) → False) ∧ ((p2 ∧ True) → False)) → False) ∨ ((((p7 ∨ p5) → (False → False)) → ((p5 ∨ p1) ∧ (True ∧ p3))) ∨ (((p7 → p4) ∧ (p2 ∨ p1)) → False))) := by
  apply Or.inl
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    have assump_33 : (p2 → False) := by
      intro assump_22
      have assump_34 : (p2 ∧ True) := by
        apply And.intro
        exact assump_22
        apply True.intro
      let assump_26 := assump_15 assump_34
      apply False.elim assump_26
    let assump_21 := assump_14 assump_33
    apply False.elim assump_21


variable (p3 p1 p2 p0 p4 p7 p5 p6 : Prop)
theorem file33_22249 : (((((p2 → False) ∨ (p0 → p7)) ∧ ((True ∧ False) ∧ (p6 ∧ True))) → False) ∨ ((((p5 → False) ∨ (p1 ∨ p4)) ∧ ((p3 ∧ p2) ∧ (p5 ∧ False))) ∨ (((p2 ∧ p4) → (p0 → False)) → ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_34
  cases assump_34
  case intro assump_35 assump_36 =>
    cases assump_35
    case inl assump_37 =>
      cases assump_36
      case intro assump_41 assump_42 =>
        cases assump_41
        case intro assump_43 assump_44 =>
          apply False.elim assump_44
    case inr assump_38 =>
      cases assump_36
      case intro assump_51 assump_52 =>
        cases assump_51
        case intro assump_53 assump_54 =>
          apply False.elim assump_54


variable (p2 p7 p5 p0 p1 p3 p4 : Prop)
theorem file33_22999 : (((((p5 ∧ p7) ∧ (p2 → p0)) → False) → (((p3 → p7) → False) ∧ ((p4 → False) → (p2 → False)))) → ((((False ∨ False) ∧ (p1 → False)) → False) ∨ (((False → p2) ∧ (p1 → False)) → ((p0 ∧ False) ∧ (False ∧ True))))) := by
  intro assump_21
  apply Or.inl
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      apply False.elim assump_27
    case inr assump_28 =>
      apply False.elim assump_28


variable (p3 p5 p1 p2 : Prop)
theorem file33_23511 : ((((((True → False) → (p5 ∧ p3)) → False) → (((p2 ∧ p5) → (True → False)) ∧ ((p1 → False) → (p3 → True)))) → False) → False) := by
  intro assump_20
  have assump_55 : ((((True → False) → (p5 ∧ p3)) → False) → (((p2 ∧ p5) → (True → False)) ∧ ((p1 → False) → (p3 → True)))) := by
    intro assump_24
    apply And.intro
    intro assump_25
    intro assump_26
    cases assump_25
    case intro assump_29 assump_30 =>
      have assump_56 : ((True → False) → (p5 ∧ p3)) := by
        intro assump_38
        apply And.intro
        exact assump_30
        have assump_57 : True := by
          apply True.intro
        let assump_43 := assump_38 assump_57
        apply False.elim assump_43
      let assump_37 := assump_24 assump_56
      apply False.elim assump_37
    intro assump_50
    intro assump_51
    apply True.intro
  let assump_23 := assump_20 assump_55
  apply False.elim assump_23


variable (p4 p6 p7 p5 p3 p1 p2 : Prop)
theorem file33_24469 : (((((True → p1) → (p5 ∨ p4)) → False) → (((p7 ∨ True) ∨ (False ∨ False)) ∨ ((p3 → False) ∨ (p7 ∨ p2)))) ∨ ((((p2 ∧ True) ∧ (p1 → False)) → ((p1 → p2) → False)) → (((p5 ∨ p7) ∧ (p1 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p7 p0 p2 p4 p5 p6 p1 : Prop)
theorem file33_24832 : ((((((True → p4) ∨ (p1 ∨ p7)) ∧ ((p6 ∧ p0) → (p0 ∨ False))) ∨ (((p6 ∧ True) ∨ (p0 ∧ p2)) ∧ ((p1 ∨ p1) → (p6 → p2)))) ∧ ((((p7 ∧ p6) → False) ∨ ((p4 ∧ False) ∧ (p6 → False))) ∧ (((p2 → False) ∧ (False ∧ p2)) ∧ ((p5 → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_23
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_26
            case inr assump_17 =>
              cases assump_17
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_33
        case inr assump_9 =>
          cases assump_9
          case inl assump_38 =>
            cases assump_3
            case intro assump_44 assump_45 =>
              cases assump_44
              case inl assump_46 =>
                cases assump_45
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    cases assump_53
                    case intro assump_56 assump_57 =>
                      apply False.elim assump_56
              case inr assump_47 =>
                cases assump_47
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    apply False.elim assump_63
          case inr assump_39 =>
            cases assump_3
            case intro assump_72 assump_73 =>
              cases assump_72
              case inl assump_74 =>
                cases assump_73
                case intro assump_78 assump_79 =>
                  cases assump_78
                  case intro assump_80 assump_81 =>
                    cases assump_81
                    case intro assump_84 assump_85 =>
                      apply False.elim assump_84
              case inr assump_75 =>
                cases assump_75
                case intro assump_88 assump_89 =>
                  cases assump_88
                  case intro assump_90 assump_91 =>
                    apply False.elim assump_91
    case inr assump_5 =>
      cases assump_5
      case intro assump_96 assump_97 =>
        cases assump_96
        case inl assump_98 =>
          cases assump_98
          case intro assump_100 assump_101 =>
            cases assump_3
            case intro assump_108 assump_109 =>
              cases assump_108
              case inl assump_110 =>
                cases assump_109
                case intro assump_114 assump_115 =>
                  cases assump_114
                  case intro assump_116 assump_117 =>
                    cases assump_117
                    case intro assump_120 assump_121 =>
                      apply False.elim assump_120
              case inr assump_111 =>
                cases assump_111
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case intro assump_126 assump_127 =>
                    apply False.elim assump_127
        case inr assump_99 =>
          cases assump_99
          case intro assump_132 assump_133 =>
            cases assump_3
            case intro assump_140 assump_141 =>
              cases assump_140
              case inl assump_142 =>
                cases assump_141
                case intro assump_146 assump_147 =>
                  cases assump_146
                  case intro assump_148 assump_149 =>
                    cases assump_149
                    case intro assump_152 assump_153 =>
                      apply False.elim assump_152
              case inr assump_143 =>
                cases assump_143
                case intro assump_156 assump_157 =>
                  cases assump_156
                  case intro assump_158 assump_159 =>
                    apply False.elim assump_159


variable (p1 p6 p4 p2 : Prop)
theorem file33_29286 : (((((p4 ∨ False) ∧ (p1 → False)) ∨ ((p4 ∧ p6) → (p2 → p2))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p4 ∨ False) ∧ (p1 → False)) ∨ ((p4 ∧ p6) → (p2 → p2))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p0 p6 p3 p7 p1 : Prop)
theorem file33_29727 : (((((p7 ∧ p3) → (True → True)) → False) → (((p7 ∨ p0) ∧ (p6 ∧ p1)) ∧ ((True ∨ p4) ∨ (p1 → p3)))) ∧ ((((False → False) → False) ∧ ((p1 ∧ p1) ∧ (p7 → False))) → False)) := by
  apply And.intro
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_53 : ((p7 ∧ p3) → (True → True)) := by
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4
  apply And.intro
  have assump_54 : ((p7 ∧ p3) → (True → True)) := by
    intro assump_13
    intro assump_14
    apply True.intro
  let assump_12 := assump_1 assump_54
  apply False.elim assump_12
  have assump_55 : ((p7 ∧ p3) → (True → True)) := by
    intro assump_21
    intro assump_22
    apply True.intro
  let assump_20 := assump_1 assump_55
  apply False.elim assump_20
  apply Or.inl
  apply Or.inl
  apply True.intro
  intro assump_28
  cases assump_28
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        have assump_56 : (False → False) := by
          intro assump_47
          apply False.elim assump_47
        let assump_46 := assump_29 assump_56
        apply False.elim assump_46


variable (p3 p1 p6 p0 p7 p4 p2 : Prop)
theorem file33_31022 : (((((p3 ∨ p6) → False) ∨ ((p6 ∧ False) ∨ (p6 ∨ p7))) → (((p1 → p1) ∧ (p4 → False)) ∨ ((p6 → False) ∧ (True → False)))) → ((((p4 ∧ p2) → (True ∧ p4)) ∧ ((True ∧ p6) ∨ (p2 → False))) → (((p2 → p4) → (p0 → False)) → ((p4 ∧ False) ∨ (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply Or.inr
        intro assump_20
        apply False.elim assump_20
    case inr assump_11 =>
      apply Or.inr
      intro assump_27
      apply False.elim assump_27


variable (p2 p3 p4 p0 p1 p5 p7 p6 : Prop)
theorem file33_31732 : ((((((p6 → p3) → False) ∨ ((p7 ∨ p7) → (True ∨ p5))) ∨ (((p7 → p2) → False) ∧ ((p7 ∧ p4) ∧ (p5 ∨ p0)))) ∧ ((((p0 ∨ p7) ∧ (p1 → False)) → ((p1 → False) ∨ (p2 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_170 : (((p0 ∨ p7) ∧ (p1 → False)) → ((p1 → False) ∨ (p2 ∨ p1))) := by
          intro assump_13
          cases assump_13
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              apply Or.inl
              intro assump_22
              have assump_171 : p1 := by
                exact assump_22
              let assump_26 := assump_15 assump_171
              apply False.elim assump_26
            case inr assump_17 =>
              apply Or.inl
              intro assump_34
              have assump_172 : p1 := by
                exact assump_34
              let assump_38 := assump_15 assump_172
              apply False.elim assump_38
        let assump_12 := assump_3 assump_170
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_173 : (((p0 ∨ p7) ∧ (p1 → False)) → ((p1 → False) ∨ (p2 ∨ p1))) := by
          intro assump_50
          cases assump_50
          case intro assump_51 assump_52 =>
            cases assump_51
            case inl assump_53 =>
              apply Or.inl
              intro assump_59
              have assump_174 : p1 := by
                exact assump_59
              let assump_63 := assump_52 assump_174
              apply False.elim assump_63
            case inr assump_54 =>
              apply Or.inl
              intro assump_71
              have assump_175 : p1 := by
                exact assump_71
              let assump_75 := assump_52 assump_175
              apply False.elim assump_75
        let assump_49 := assump_3 assump_173
        apply False.elim assump_49
    case inr assump_5 =>
      cases assump_5
      case intro assump_82 assump_83 =>
        cases assump_83
        case intro assump_86 assump_87 =>
          cases assump_86
          case intro assump_88 assump_89 =>
            cases assump_87
            case inl assump_94 =>
              have assump_176 : (((p0 ∨ p7) ∧ (p1 → False)) → ((p1 → False) ∨ (p2 ∨ p1))) := by
                intro assump_101
                cases assump_101
                case intro assump_102 assump_103 =>
                  cases assump_102
                  case inl assump_104 =>
                    apply Or.inl
                    intro assump_110
                    have assump_177 : p1 := by
                      exact assump_110
                    let assump_114 := assump_103 assump_177
                    apply False.elim assump_114
                  case inr assump_105 =>
                    apply Or.inl
                    intro assump_122
                    have assump_178 : p1 := by
                      exact assump_122
                    let assump_126 := assump_103 assump_178
                    apply False.elim assump_126
              let assump_100 := assump_3 assump_176
              apply False.elim assump_100
            case inr assump_95 =>
              have assump_179 : (((p0 ∨ p7) ∧ (p1 → False)) → ((p1 → False) ∨ (p2 ∨ p1))) := by
                intro assump_138
                cases assump_138
                case intro assump_139 assump_140 =>
                  cases assump_139
                  case inl assump_141 =>
                    apply Or.inl
                    intro assump_147
                    have assump_180 : p1 := by
                      exact assump_147
                    let assump_151 := assump_140 assump_180
                    apply False.elim assump_151
                  case inr assump_142 =>
                    apply Or.inl
                    intro assump_159
                    have assump_181 : p1 := by
                      exact assump_159
                    let assump_163 := assump_140 assump_181
                    apply False.elim assump_163
              let assump_137 := assump_3 assump_179
              apply False.elim assump_137


variable (p0 p7 p3 p4 p1 p2 p6 : Prop)
theorem file33_36012 : (((((p1 → False) ∨ (p1 ∧ p1)) → False) → (((p1 ∧ p3) ∨ (p3 ∧ p6)) ∨ ((p4 ∧ False) ∧ (p4 → False)))) → ((((False ∧ p1) ∨ (p2 → p0)) → False) → (((p7 → False) → False) → ((True → False) → (False → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p3 p5 p1 p6 p2 : Prop)
theorem file33_36384 : ((((((p5 ∨ p1) → (True ∨ p1)) ∧ ((p1 ∧ False) ∧ (p1 → False))) ∨ (((p6 ∨ p3) ∨ (p2 ∧ p5)) → ((False → False) ∨ (p1 → p1)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p5 ∨ p1) → (True ∨ p1)) ∧ ((p1 ∧ False) ∧ (p1 → False))) ∨ (((p6 ∨ p3) ∨ (p2 ∧ p5)) → ((False → False) ∨ (p1 → p1)))) := by
    apply Or.inr
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inl
        intro assump_19
        apply False.elim assump_19
      case inr assump_16 =>
        apply Or.inl
        intro assump_24
        apply False.elim assump_24
    case inr assump_14 =>
      cases assump_14
      case intro assump_27 assump_28 =>
        apply Or.inl
        intro assump_33
        apply False.elim assump_33
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p7 p6 p5 p0 p3 p2 p4 p1 : Prop)
theorem file33_37316 : (((((p0 → False) → (p1 → p4)) ∨ ((p1 ∧ p7) ∨ (p6 → False))) ∧ (((p7 ∧ p1) → (p4 ∧ p1)) ∧ ((p4 ∨ False) ∧ (p4 → p6)))) → ((((True ∨ p7) → False) → False) ∨ (((p2 ∧ p5) ∨ (False ∧ p3)) ∨ ((p1 → p3) → False)))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_16
          case inl assump_18 =>
            apply Or.inl
            intro assump_24
            have assump_85 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_27 := assump_24 assump_85
            apply False.elim assump_27
          case inr assump_19 =>
            apply False.elim assump_19
    case inr assump_9 =>
      cases assump_9
      case inl assump_33 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_7
          case intro assump_41 assump_42 =>
            cases assump_42
            case intro assump_45 assump_46 =>
              cases assump_45
              case inl assump_47 =>
                apply Or.inl
                intro assump_53
                have assump_86 : (True ∨ p7) := by
                  apply Or.inl
                  apply True.intro
                let assump_56 := assump_53 assump_86
                apply False.elim assump_56
              case inr assump_48 =>
                apply False.elim assump_48
      case inr assump_34 =>
        cases assump_7
        case intro assump_64 assump_65 =>
          cases assump_65
          case intro assump_68 assump_69 =>
            cases assump_68
            case inl assump_70 =>
              apply Or.inl
              intro assump_76
              have assump_87 : (True ∨ p7) := by
                apply Or.inl
                apply True.intro
              let assump_79 := assump_76 assump_87
              apply False.elim assump_79
            case inr assump_71 =>
              apply False.elim assump_71


variable (p0 p2 p5 p6 p4 p3 p7 : Prop)
theorem file33_39469 : ((((((p2 ∨ p4) ∧ (True → False)) → False) ∨ (((p6 ∧ p0) ∧ (p7 ∧ p3)) → ((p5 → p3) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p2 ∨ p4) ∧ (True → False)) → False) ∨ (((p6 ∧ p0) ∧ (p7 ∧ p3)) → ((p5 → p3) → False))) := by
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


variable (p2 p0 p4 p1 p3 p6 p7 p5 : Prop)
theorem file33_40300 : (((((p4 → True) → (True → False)) → ((p3 → p1) ∨ (p7 → p1))) ∧ (((p2 ∧ p2) → (p0 → True)) → False)) → ((((p0 → False) ∨ (p2 ∧ p6)) ∨ ((p4 ∧ p5) ∨ (p6 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        have assump_65 : ((p2 ∧ p2) → (p0 → True)) := by
          intro assump_16
          intro assump_17
          apply True.intro
        let assump_15 := assump_10 assump_65
        apply False.elim assump_15
    case inr assump_6 =>
      cases assump_6
      case intro assump_21 assump_22 =>
        cases assump_1
        case intro assump_27 assump_28 =>
          have assump_66 : ((p2 ∧ p2) → (p0 → True)) := by
            intro assump_34
            intro assump_35
            apply True.intro
          let assump_33 := assump_28 assump_66
          apply False.elim assump_33
  case inr assump_4 =>
    cases assump_4
    case inl assump_39 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        cases assump_1
        case intro assump_47 assump_48 =>
          have assump_67 : ((p2 ∧ p2) → (p0 → True)) := by
            intro assump_54
            intro assump_55
            apply True.intro
          let assump_53 := assump_48 assump_67
          apply False.elim assump_53
    case inr assump_40 =>
      cases assump_40
      case intro assump_59 assump_60 =>
        apply False.elim assump_60


variable (p2 p6 p1 p7 p4 : Prop)
theorem file33_41853 : ((((((p6 → False) → (p1 → False)) ∧ ((p4 → False) → False)) ∧ (((p7 → False) ∧ (p7 → p4)) → False)) ∧ ((((False → False) ∧ (p1 ∨ p2)) → ((True ∧ p6) → False)) ∧ (((True ∧ p1) → False) ∧ ((True → False) ∧ (p1 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                apply False.elim assump_27


variable (p6 p1 p7 p0 p2 : Prop)
theorem file33_42658 : ((((((p1 ∧ p6) ∨ (p0 ∨ p1)) → False) → (((p1 ∨ p2) → (p0 ∨ p1)) → ((p2 ∨ False) → (p7 → False)))) → False) → False) := by
  intro assump_5
  have assump_47 : ((((p1 ∧ p6) ∨ (p0 ∨ p1)) → False) → (((p1 ∨ p2) → (p0 ∨ p1)) → ((p2 ∨ False) → (p7 → False)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    intro assump_12
    cases assump_11
    case inl assump_15 =>
      have assump_48 : (p1 ∨ p2) := by
        apply Or.inr
        exact assump_15
      let assump_24 := assump_10 assump_48
      cases assump_24
      case inl assump_26 =>
        have assump_49 : ((p1 ∧ p6) ∨ (p0 ∨ p1)) := by
          apply Or.inr
          apply Or.inl
          exact assump_26
        let assump_31 := assump_9 assump_49
        apply False.elim assump_31
      case inr assump_27 =>
        have assump_50 : ((p1 ∧ p6) ∨ (p0 ∨ p1)) := by
          apply Or.inr
          apply Or.inr
          exact assump_27
        let assump_38 := assump_9 assump_50
        apply False.elim assump_38
    case inr assump_16 =>
      apply False.elim assump_16
  let assump_8 := assump_5 assump_47
  apply False.elim assump_8


variable (p2 p1 p6 p0 : Prop)
theorem file33_43838 : (((((False → False) ∨ (p0 → p1)) ∧ ((p2 → True) ∨ (p0 ∧ p6))) → False) → False) := by
  intro assump_66
  have assump_77 : (((False → False) ∨ (p0 → p1)) ∧ ((p2 → True) ∨ (p0 ∧ p6))) := by
    apply And.intro
    apply Or.inl
    intro assump_70
    apply False.elim assump_70
    apply Or.inl
    intro assump_73
    apply True.intro
  let assump_69 := assump_66 assump_77
  apply False.elim assump_69


variable (p4 p2 p1 p7 p6 : Prop)
theorem file33_44298 : (((((p6 ∨ p7) ∧ (p7 ∧ p2)) ∨ ((p2 ∨ p2) ∨ (p6 → p4))) ∧ (((p7 → False) ∧ (False ∧ p1)) ∧ ((False ∨ p1) → (p1 ∧ p4)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  apply False.elim assump_28
        case inr assump_13 =>
          cases assump_11
          case intro assump_34 assump_35 =>
            cases assump_7
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_43
                case intro assump_46 assump_47 =>
                  apply False.elim assump_46
    case inr assump_9 =>
      cases assump_9
      case inl assump_50 =>
        cases assump_50
        case inl assump_52 =>
          cases assump_7
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                apply False.elim assump_62
        case inr assump_53 =>
          cases assump_7
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_71
              case intro assump_74 assump_75 =>
                apply False.elim assump_74
      case inr assump_51 =>
        cases assump_7
        case intro assump_80 assump_81 =>
          cases assump_80
          case intro assump_82 assump_83 =>
            cases assump_83
            case intro assump_86 assump_87 =>
              apply False.elim assump_86


variable (p6 p2 p1 p3 p5 p7 p0 : Prop)
theorem file33_46411 : (((((p2 → p6) ∨ (p6 ∧ p5)) ∧ ((p7 → False) → False)) → (((p6 ∧ True) ∨ (p3 → p2)) → ((True ∨ p0) ∨ (False → p5)))) ∨ ((((p0 → p1) ∨ (p6 → False)) → ((p0 → p5) → False)) → (((p2 → p3) → (p2 ∨ p6)) ∧ ((p2 → p0) ∨ (p6 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_14 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
  case inr assump_4 =>
    cases assump_1
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_32 =>
        cases assump_32
        case intro assump_37 assump_38 =>
          apply Or.inl
          apply Or.inl
          apply True.intro


variable (p7 p6 p1 p2 p3 p5 : Prop)
theorem file33_47579 : (((((p3 ∨ False) → (p2 → p2)) ∨ ((True → False) → (p2 ∧ p1))) ∨ (((False → p7) ∧ (p3 ∧ True)) → ((p5 ∧ p6) → (True → p2)))) ∨ ((((False ∧ p7) → (p3 → False)) ∧ ((p1 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    exact assump_2
  case inr assump_6 =>
    apply False.elim assump_6


variable (p5 p7 p4 p2 p1 p3 p6 : Prop)
theorem file33_48033 : (((((p1 ∧ p7) ∨ (p5 → False)) → False) ∧ (((False → False) ∨ (p2 → False)) ∧ ((p4 → False) → False))) → ((((p5 ∧ p5) ∨ (p4 ∨ p3)) → ((p5 → False) → False)) → (((p6 ∨ True) ∨ (True ∧ p2)) ∨ ((p1 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p1 p3 p5 p6 : Prop)
theorem file33_48702 : (((((p6 → False) ∨ (p6 ∧ True)) ∧ ((p5 → True) ∧ (p3 → True))) ∧ (((False → False) → False) ∧ ((p6 ∨ p5) ∨ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case inl assump_22 =>
                have assump_104 : (False → False) := by
                  intro assump_28
                  apply False.elim assump_28
                let assump_27 := assump_16 assump_104
                apply False.elim assump_27
              case inr assump_23 =>
                have assump_105 : (False → False) := by
                  intro assump_38
                  apply False.elim assump_38
                let assump_37 := assump_16 assump_105
                apply False.elim assump_37
            case inr assump_21 =>
              have assump_106 : (False → False) := by
                intro assump_48
                apply False.elim assump_48
              let assump_47 := assump_16 assump_106
              apply False.elim assump_47
      case inr assump_7 =>
        cases assump_7
        case intro assump_54 assump_55 =>
          cases assump_5
          case intro assump_60 assump_61 =>
            cases assump_3
            case intro assump_66 assump_67 =>
              cases assump_67
              case inl assump_70 =>
                cases assump_70
                case inl assump_72 =>
                  have assump_107 : (False → False) := by
                    intro assump_78
                    apply False.elim assump_78
                  let assump_77 := assump_66 assump_107
                  apply False.elim assump_77
                case inr assump_73 =>
                  have assump_108 : (False → False) := by
                    intro assump_88
                    apply False.elim assump_88
                  let assump_87 := assump_66 assump_108
                  apply False.elim assump_87
              case inr assump_71 =>
                have assump_109 : (False → False) := by
                  intro assump_98
                  apply False.elim assump_98
                let assump_97 := assump_66 assump_109
                apply False.elim assump_97


variable (p3 p7 p0 p5 p1 : Prop)
theorem file33_51246 : (((((False → False) ∨ (p1 ∨ True)) ∨ ((p3 → p3) ∨ (p5 → False))) ∨ (((p1 → p1) → False) ∧ ((p3 ∨ p7) ∨ (p3 → False)))) ∨ ((((p0 ∨ True) ∨ (p3 → p3)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p1 p0 p2 p6 p4 p5 p7 p3 : Prop)
theorem file33_51591 : ((((((p7 ∨ p0) → False) → False) → (((p1 ∨ p6) → False) ∧ ((p3 ∨ p5) → (False → p0)))) ∧ ((((p2 ∧ p0) ∧ (True → False)) ∨ ((p6 → p0) → (False ∧ p1))) ∧ (((p0 → p5) → (p4 → p4)) → False))) → False) := by
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
            have assump_46 : ((p0 → p5) → (p4 → p4)) := by
              intro assump_23
              intro assump_24
              exact assump_24
            let assump_22 := assump_7 assump_46
            apply False.elim assump_22
      case inr assump_9 =>
        have assump_47 : ((p0 → p5) → (p4 → p4)) := by
          intro assump_37
          intro assump_38
          exact assump_38
        let assump_36 := assump_7 assump_47
        apply False.elim assump_36


variable (p7 p2 p0 p1 p5 p4 p3 : Prop)
theorem file33_52638 : (((((p7 ∨ False) → (p4 → p3)) ∨ ((p2 ∧ p3) ∧ (False → p4))) ∧ (((p1 → p0) ∧ (p2 → False)) ∧ ((p5 → p5) ∧ (p3 ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_68 : p2 := by
                exact assump_21
              let assump_29 := assump_11 assump_68
              apply False.elim assump_29
    case inr assump_5 =>
      cases assump_5
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_3
          case intro assump_43 assump_44 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              cases assump_44
              case intro assump_51 assump_52 =>
                cases assump_52
                case intro assump_55 assump_56 =>
                  have assump_69 : p2 := by
                    exact assump_56
                  let assump_64 := assump_46 assump_69
                  apply False.elim assump_64


variable (p2 p0 p7 : Prop)
theorem file33_54000 : ((((((False → True) → False) → ((True → False) → (p0 → False))) ∨ (((p2 ∨ p7) ∨ (p7 ∨ p0)) → False)) → False) → False) := by
  intro assump_14
  have assump_35 : ((((False → True) → False) → ((True → False) → (p0 → False))) ∨ (((p2 ∨ p7) ∨ (p7 ∨ p0)) → False)) := by
    apply Or.inl
    intro assump_18
    intro assump_19
    intro assump_20
    have assump_36 : (False → True) := by
      intro assump_28
      apply True.intro
    let assump_27 := assump_18 assump_36
    apply False.elim assump_27
  let assump_17 := assump_14 assump_35
  apply False.elim assump_17


variable (p7 p2 p6 p0 p4 p1 : Prop)
theorem file33_54631 : (((((False ∧ p0) ∧ (p7 → False)) ∧ ((p1 → p1) → False)) ∧ (((False ∧ p4) ∨ (p2 ∨ p1)) ∧ ((p6 ∧ p0) → False))) → False) := by
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


variable (p3 p6 p2 p4 p1 : Prop)
theorem file33_55094 : (((((p3 ∨ p6) ∨ (False → False)) → False) ∧ (((p2 ∧ p4) → False) ∨ ((p1 ∨ False) ∧ (p6 ∧ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_39 : ((p3 ∨ p6) ∨ (False → False)) := by
        apply Or.inr
        intro assump_12
        apply False.elim assump_12
      let assump_11 := assump_2 assump_39
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_19
          case intro assump_24 assump_25 =>
            have assump_40 : ((p3 ∨ p6) ∨ (False → False)) := by
              apply Or.inl
              apply Or.inr
              exact assump_24
            let assump_33 := assump_2 assump_40
            apply False.elim assump_33
        case inr assump_21 =>
          apply False.elim assump_21


variable (p0 p6 p3 p7 p1 p2 : Prop)
theorem file33_56104 : (((((False ∧ p3) ∧ (p2 → False)) → False) → False) → ((((p6 → False) ∧ (p2 ∧ p2)) ∨ ((p0 → False) → (p1 → False))) → (((p1 → False) ∧ (p7 ∨ p0)) → False))) := by
  intro assump_41
  intro assump_42
  intro assump_43
  cases assump_43
  case intro assump_44 assump_45 =>
    cases assump_45
    case inl assump_48 =>
      cases assump_42
      case inl assump_52 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          cases assump_55
          case intro assump_58 assump_59 =>
            have assump_134 : (((False ∧ p3) ∧ (p2 → False)) → False) := by
              intro assump_67
              cases assump_67
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  apply False.elim assump_70
            let assump_66 := assump_41 assump_134
            apply False.elim assump_66
      case inr assump_53 =>
        have assump_135 : (((False ∧ p3) ∧ (p2 → False)) → False) := by
          intro assump_82
          cases assump_82
          case intro assump_83 assump_84 =>
            cases assump_83
            case intro assump_85 assump_86 =>
              apply False.elim assump_85
        let assump_81 := assump_41 assump_135
        apply False.elim assump_81
    case inr assump_49 =>
      cases assump_42
      case inl assump_94 =>
        cases assump_94
        case intro assump_96 assump_97 =>
          cases assump_97
          case intro assump_100 assump_101 =>
            have assump_136 : (((False ∧ p3) ∧ (p2 → False)) → False) := by
              intro assump_109
              cases assump_109
              case intro assump_110 assump_111 =>
                cases assump_110
                case intro assump_112 assump_113 =>
                  apply False.elim assump_112
            let assump_108 := assump_41 assump_136
            apply False.elim assump_108
      case inr assump_95 =>
        have assump_137 : (((False ∧ p3) ∧ (p2 → False)) → False) := by
          intro assump_124
          cases assump_124
          case intro assump_125 assump_126 =>
            cases assump_125
            case intro assump_127 assump_128 =>
              apply False.elim assump_127
        let assump_123 := assump_41 assump_137
        apply False.elim assump_123


variable (p6 p0 p4 p7 p5 p2 p1 : Prop)
theorem file33_58487 : ((((((p6 ∧ p0) → (p0 ∨ p1)) ∧ ((True → False) ∧ (p6 ∧ p1))) → (((p0 ∧ p7) → (p4 → p6)) → ((p5 ∧ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p6 ∧ p0) → (p0 ∨ p1)) ∧ ((True → False) ∧ (p6 ∧ p1))) → (((p0 ∧ p7) → (p4 → p6)) → ((p5 ∧ p2) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_21
          case intro assump_24 assump_25 =>
            have assump_40 : True := by
              apply True.intro
            let assump_32 := assump_20 assump_40
            apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p5 p0 p6 p7 p3 p2 p4 p1 : Prop)
theorem file33_59372 : (((((p5 ∧ p1) → (p5 → p0)) → ((False → p6) → (True → False))) → (((p0 ∧ p3) → False) ∨ ((p4 ∧ p4) → (True → p6)))) ∨ ((((p7 ∨ p5) ∧ (p4 ∨ False)) → ((p5 → p6) → False)) → (((p4 → False) ∨ (p2 → p3)) → ((True → False) ∧ (p2 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_32 : ((p5 ∧ p1) → (p5 → p0)) := by
      intro assump_14
      intro assump_15
      cases assump_14
      case intro assump_18 assump_19 =>
        exact assump_5
    let assump_13 := assump_1 assump_32
    have assump_33 : (False → p6) := by
      intro assump_25
      apply False.elim assump_25
    let assump_24 := assump_13 assump_33
    have assump_34 : True := by
      apply True.intro
    let assump_28 := assump_24 assump_34
    apply False.elim assump_28


variable (p7 p4 p0 p2 p6 p5 p1 p3 : Prop)
theorem file33_60275 : ((((((p2 → p0) ∧ (p0 → p6)) ∨ ((True ∧ p0) → (p6 → p7))) ∨ (((p5 → False) → False) ∧ ((True ∧ p4) ∨ (p1 ∨ True)))) ∧ ((((False ∧ p3) ∧ (p5 ∨ p2)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          have assump_99 : (((False ∧ p3) ∧ (p5 ∨ p2)) → False) := by
            intro assump_17
            cases assump_17
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
          let assump_16 := assump_3 assump_99
          apply False.elim assump_16
      case inr assump_7 =>
        have assump_100 : (((False ∧ p3) ∧ (p5 ∨ p2)) → False) := by
          intro assump_32
          cases assump_32
          case intro assump_33 assump_34 =>
            cases assump_33
            case intro assump_35 assump_36 =>
              apply False.elim assump_35
        let assump_31 := assump_3 assump_100
        apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case intro assump_42 assump_43 =>
        cases assump_43
        case inl assump_46 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            have assump_101 : (((False ∧ p3) ∧ (p5 ∨ p2)) → False) := by
              intro assump_57
              cases assump_57
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  apply False.elim assump_60
            let assump_56 := assump_3 assump_101
            apply False.elim assump_56
        case inr assump_47 =>
          cases assump_47
          case inl assump_67 =>
            have assump_102 : (((False ∧ p3) ∧ (p5 ∨ p2)) → False) := by
              intro assump_74
              cases assump_74
              case intro assump_75 assump_76 =>
                cases assump_75
                case intro assump_77 assump_78 =>
                  apply False.elim assump_77
            let assump_73 := assump_3 assump_102
            apply False.elim assump_73
          case inr assump_68 =>
            have assump_103 : (((False ∧ p3) ∧ (p5 ∨ p2)) → False) := by
              intro assump_89
              cases assump_89
              case intro assump_90 assump_91 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  apply False.elim assump_92
            let assump_88 := assump_3 assump_103
            apply False.elim assump_88


variable (p0 p1 p7 p2 p3 p5 : Prop)
theorem file33_63019 : (((((p7 → False) → False) ∧ ((p5 → True) → False)) → (((True ∧ False) → False) ∨ ((p7 ∨ p0) ∧ (p0 → False)))) ∨ ((((False → False) ∧ (p7 → False)) ∧ ((p7 ∨ p0) → (p7 ∧ False))) → (((True → p5) → (p3 ∧ p0)) ∧ ((True → p1) ∧ (True ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10


variable (p2 p3 p4 p1 p6 p5 p0 : Prop)
theorem file33_63535 : ((((((p5 ∨ p5) → False) ∧ ((False ∨ p1) → False)) ∧ (((False → p5) → False) → ((p3 ∨ p6) ∨ (p5 ∨ p3)))) ∧ ((((p3 ∧ False) ∨ (p4 → False)) → ((False → False) ∨ (p1 ∨ False))) → (((p0 ∨ p5) → False) ∧ ((p0 ∨ False) ∨ (p0 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_91 : (((p3 ∧ False) ∨ (p4 → False)) → ((False → False) ∨ (p1 ∨ False))) := by
          intro assump_17
          cases assump_17
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
          case inr assump_19 =>
            apply Or.inl
            intro assump_28
            apply False.elim assump_28
        let assump_16 := assump_3 assump_91
        let assump_31 := And.right assump_16
        cases assump_31
        case inl assump_34 =>
          cases assump_34
          case inl assump_36 =>
            have assump_92 : (((p3 ∧ False) ∨ (p4 → False)) → ((False → False) ∨ (p1 ∨ False))) := by
              intro assump_42
              cases assump_42
              case inl assump_43 =>
                cases assump_43
                case intro assump_45 assump_46 =>
                  apply False.elim assump_46
              case inr assump_44 =>
                apply Or.inl
                intro assump_53
                apply False.elim assump_53
            let assump_41 := assump_3 assump_92
            let assump_56 := And.left assump_41
            have assump_93 : (p0 ∨ p5) := by
              apply Or.inl
              exact assump_36
            let assump_57 := assump_56 assump_93
            apply False.elim assump_57
          case inr assump_37 =>
            apply False.elim assump_37
        case inr assump_35 =>
          cases assump_35
          case intro assump_63 assump_64 =>
            have assump_94 : (((p3 ∧ False) ∨ (p4 → False)) → ((False → False) ∨ (p1 ∨ False))) := by
              intro assump_72
              cases assump_72
              case inl assump_73 =>
                cases assump_73
                case intro assump_75 assump_76 =>
                  apply False.elim assump_76
              case inr assump_74 =>
                apply Or.inl
                intro assump_83
                apply False.elim assump_83
            let assump_71 := assump_3 assump_94
            let assump_86 := And.left assump_71
            have assump_95 : (p0 ∨ p5) := by
              apply Or.inl
              exact assump_63
            let assump_87 := assump_86 assump_95
            apply False.elim assump_87


variable (p1 p4 p5 p3 p0 p2 p6 p7 : Prop)
theorem file33_66322 : (((((p4 ∧ p0) → (p0 → p4)) → False) → (((p7 → p1) → (p3 → False)) ∧ ((p0 → False) ∧ (p7 → p5)))) ∨ ((((p2 → False) ∨ (True → p4)) → ((p6 → False) ∨ (p5 ∨ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_62 : ((p4 ∧ p0) → (p0 → p4)) := by
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      exact assump_15
  let assump_10 := assump_1 assump_62
  apply False.elim assump_10
  apply And.intro
  intro assump_24
  have assump_63 : ((p4 ∧ p0) → (p0 → p4)) := by
    intro assump_30
    intro assump_31
    cases assump_30
    case intro assump_34 assump_35 =>
      exact assump_34
  let assump_29 := assump_1 assump_63
  apply False.elim assump_29
  intro assump_43
  have assump_64 : ((p4 ∧ p0) → (p0 → p4)) := by
    intro assump_49
    intro assump_50
    cases assump_49
    case intro assump_53 assump_54 =>
      exact assump_53
  let assump_48 := assump_1 assump_64
  apply False.elim assump_48


variable (p3 : Prop)
theorem file33_67389 : (((((p3 → False) → False) → False) ∧ (((True → False) → False) → False)) → False) := by
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


variable (p1 p6 p4 p0 p7 p2 p5 : Prop)
theorem file33_67884 : (((((p6 → p4) → False) ∧ ((True → False) ∨ (p2 → p0))) → (((p7 ∨ p5) ∨ (False → False)) ∨ ((p1 ∧ p0) ∧ (True → False)))) ∨ ((((True ∧ p0) ∧ (p0 ∨ p1)) → ((p6 → False) → False)) ∨ (((p2 → p7) → False) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      apply Or.inl
      apply Or.inr
      intro assump_15
      apply False.elim assump_15


variable (p0 p7 p1 p4 p3 p2 p6 : Prop)
theorem file33_68502 : ((((((p3 → p3) ∨ (p4 → False)) ∧ ((p7 ∧ p2) → (p4 ∨ p7))) ∨ (((p6 ∨ p1) ∧ (p3 → p0)) → ((p6 ∧ p4) ∨ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p3 → p3) ∨ (p4 → False)) ∧ ((p7 ∧ p2) → (p4 ∨ p7))) ∨ (((p6 ∨ p1) ∧ (p3 → p0)) → ((p6 ∧ p4) ∨ (p7 → False)))) := by
    apply Or.inl
    apply And.intro
    apply Or.inl
    intro assump_5
    exact assump_5
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inr
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p5 p4 p3 : Prop)
theorem file33_69124 : ((((((p7 ∧ p3) → (p5 ∨ p3)) → False) → (((p5 → False) → False) ∧ ((p7 → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p7 ∧ p3) → (p5 ∨ p3)) → False) → (((p5 → False) → False) ∧ ((p7 → p4) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_42 : ((p7 ∧ p3) → (p5 ∨ p3)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inr
        exact assump_14
    let assump_11 := assump_5 assump_42
    apply False.elim assump_11
    intro assump_22
    have assump_43 : ((p7 ∧ p3) → (p5 ∨ p3)) := by
      intro assump_28
      cases assump_28
      case intro assump_29 assump_30 =>
        apply Or.inr
        exact assump_30
    let assump_27 := assump_5 assump_43
    apply False.elim assump_27
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p5 p1 p6 p4 : Prop)
theorem file33_70061 : ((((((p6 ∧ False) → (p4 ∨ p5)) → False) → (((p1 ∨ p5) → (True → False)) → ((p5 → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 ∧ False) → (p4 ∨ p5)) → False) → (((p1 ∨ p5) → (True → False)) → ((p5 → p4) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_29 : ((p6 ∧ False) → (p4 ∨ p5)) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    let assump_14 := assump_5 assump_29
    apply False.elim assump_14
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p7 p0 p3 p2 : Prop)
theorem file33_70737 : (((((p2 → False) → False) → ((True ∨ p7) → False)) ∧ (((p0 → p3) → False) ∧ ((p7 ∨ p0) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_25 : (p0 → p3) := by
        intro assump_14
        have assump_26 : (p7 ∨ p0) := by
          apply Or.inr
          exact assump_14
        let assump_18 := assump_7 assump_26
        apply False.elim assump_18
      let assump_13 := assump_6 assump_25
      apply False.elim assump_13


variable (p2 p7 p1 p4 p3 p6 : Prop)
theorem file33_71340 : (((((p1 ∧ p7) → (p4 → p1)) → False) → False) ∨ ((((p6 ∧ p1) ∧ (p2 ∨ p1)) → False) ∨ (((p2 ∧ p2) → (p7 → p3)) ∧ ((p6 → p2) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((p1 ∧ p7) → (p4 → p1)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p1 p3 p6 p5 p0 p7 : Prop)
theorem file33_71804 : ((((((p7 ∨ p1) ∧ (p6 ∨ p5)) ∨ ((p0 → False) → (p0 ∨ p2))) → False) ∧ ((((False ∧ p3) ∨ (True → False)) → ((p2 ∧ p0) ∧ (p3 ∧ p7))) ∧ (((p3 ∧ p0) ∧ (p0 → False)) ∧ ((p2 ∧ p3) → (p1 ∨ p2))))) → False) := by
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
            have assump_29 : p0 := by
              exact assump_15
            let assump_25 := assump_13 assump_29
            apply False.elim assump_25


variable (p2 p7 p5 p0 : Prop)
theorem file33_72538 : (((((p5 ∨ p0) → (False → False)) ∨ ((p7 ∧ p5) ∧ (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p5 ∨ p0) → (False → False)) ∨ ((p7 ∧ p5) ∧ (p2 → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p0 p4 p6 p7 p3 p2 p5 : Prop)
theorem file33_72941 : (((((p3 ∨ p7) ∨ (p0 → False)) ∧ ((True ∧ p0) → False)) → (((p5 → p5) ∨ (p5 → False)) ∨ ((p0 ∧ p6) → (p0 → False)))) ∨ ((((p5 → False) → (p5 → False)) ∨ ((p2 → p0) → (p4 → False))) ∧ (((p5 ∧ False) → False) ∨ ((True ∨ p0) ∨ (True → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        exact assump_12
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        intro assump_19
        exact assump_19
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_26
      exact assump_26


variable (p0 p7 p6 p4 p5 p1 p3 p2 : Prop)
theorem file33_73744 : ((((((p0 ∧ False) ∧ (p2 ∨ p5)) ∧ ((True → p0) → False)) ∧ (((p0 → False) ∨ (p7 → p4)) ∧ ((True → p1) ∨ (p4 → False)))) ∧ ((((p0 ∧ p7) → (p4 ∧ p6)) ∨ ((p5 → False) ∧ (p3 → True))) ∨ (((p6 ∨ p2) ∧ (p2 → p0)) ∧ ((p4 → False) → False)))) → False) := by
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
            apply False.elim assump_11


variable (p3 p7 p1 p0 p6 p5 p4 p2 : Prop)
theorem file33_74412 : (((((p7 ∧ p3) ∧ (p6 → False)) ∧ ((p6 → False) ∨ (p0 → p3))) ∨ (((p3 → False) ∨ (p1 ∨ p7)) ∨ ((p2 ∨ False) ∨ (p5 → False)))) → ((((p5 ∨ False) → False) ∧ ((False → p4) → (p3 → False))) → (((p2 ∨ p0) → (False → False)) ∨ ((p1 ∧ p1) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_12
            case inl assump_23 =>
              apply Or.inl
              intro assump_27
              intro assump_28
              apply False.elim assump_28
            case inr assump_24 =>
              apply Or.inl
              intro assump_33
              intro assump_34
              apply False.elim assump_34
    case inr assump_10 =>
      cases assump_10
      case inl assump_37 =>
        cases assump_37
        case inl assump_39 =>
          apply Or.inl
          intro assump_43
          intro assump_44
          apply False.elim assump_44
        case inr assump_40 =>
          cases assump_40
          case inl assump_47 =>
            apply Or.inl
            intro assump_51
            intro assump_52
            apply False.elim assump_52
          case inr assump_48 =>
            apply Or.inl
            intro assump_57
            intro assump_58
            apply False.elim assump_58
      case inr assump_38 =>
        cases assump_38
        case inl assump_61 =>
          cases assump_61
          case inl assump_63 =>
            apply Or.inl
            intro assump_67
            intro assump_68
            apply False.elim assump_68
          case inr assump_64 =>
            apply False.elim assump_64
        case inr assump_62 =>
          apply Or.inl
          intro assump_75
          intro assump_76
          apply False.elim assump_76


variable (p2 p1 p6 p4 p7 p3 p0 : Prop)
theorem file33_76476 : (((((p1 → p6) → False) ∧ ((p6 → False) → False)) → (((p3 ∨ p3) → (p3 ∨ False)) ∨ ((p7 ∨ True) ∧ (p1 ∧ False)))) ∨ ((((p0 → p0) → False) → False) ∧ (((p4 ∧ p2) → False) → False))) := by
  apply Or.inl
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply Or.inl
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      apply Or.inl
      exact assump_18
    case inr assump_19 =>
      apply Or.inl
      exact assump_19


variable (p6 p0 p2 p4 : Prop)
theorem file33_76993 : (((((p6 → False) ∧ (p2 → True)) ∨ ((True → False) → False)) ∧ (((False ∧ p6) → (p0 ∨ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        have assump_36 : ((False ∧ p6) → (p0 ∨ p4)) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        let assump_14 := assump_3 assump_36
        apply False.elim assump_14
    case inr assump_5 =>
      have assump_37 : ((False ∧ p6) → (p0 ∨ p4)) := by
        intro assump_28
        cases assump_28
        case intro assump_29 assump_30 =>
          apply False.elim assump_29
      let assump_27 := assump_3 assump_37
      apply False.elim assump_27


variable (p4 p0 p6 p5 p3 p7 p1 : Prop)
theorem file33_77897 : (((((p3 ∧ p5) ∧ (p4 ∨ p3)) ∧ ((p0 ∨ p3) → False)) ∧ (((p4 → True) → (p7 → p5)) ∨ ((p1 → False) ∧ (p3 ∧ p6)))) → ((((p1 → False) → (False → False)) → False) ∧ (((p0 ∧ p4) → False) ∧ ((p1 ∨ p5) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_10
          case inl assump_17 =>
            cases assump_6
            case inl assump_23 =>
              have assump_329 : (p0 ∨ p3) := by
                apply Or.inr
                exact assump_11
              let assump_30 := assump_8 assump_329
              apply False.elim assump_30
            case inr assump_24 =>
              cases assump_24
              case intro assump_34 assump_35 =>
                cases assump_35
                case intro assump_38 assump_39 =>
                  have assump_330 : (p0 ∨ p3) := by
                    apply Or.inr
                    exact assump_38
                  let assump_47 := assump_8 assump_330
                  apply False.elim assump_47
          case inr assump_18 =>
            cases assump_6
            case inl assump_55 =>
              have assump_331 : (p0 ∨ p3) := by
                apply Or.inr
                exact assump_18
              let assump_62 := assump_8 assump_331
              apply False.elim assump_62
            case inr assump_56 =>
              cases assump_56
              case intro assump_66 assump_67 =>
                cases assump_67
                case intro assump_70 assump_71 =>
                  have assump_332 : (p0 ∨ p3) := by
                    apply Or.inr
                    exact assump_70
                  let assump_79 := assump_8 assump_332
                  apply False.elim assump_79
  apply And.intro
  intro assump_83
  cases assump_83
  case intro assump_84 assump_85 =>
    cases assump_1
    case intro assump_90 assump_91 =>
      cases assump_90
      case intro assump_92 assump_93 =>
        cases assump_92
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            cases assump_95
            case inl assump_102 =>
              cases assump_91
              case inl assump_108 =>
                have assump_333 : (p0 ∨ p3) := by
                  apply Or.inl
                  exact assump_84
                let assump_115 := assump_93 assump_333
                apply False.elim assump_115
              case inr assump_109 =>
                cases assump_109
                case intro assump_119 assump_120 =>
                  cases assump_120
                  case intro assump_123 assump_124 =>
                    have assump_334 : (p0 ∨ p3) := by
                      apply Or.inl
                      exact assump_84
                    let assump_132 := assump_93 assump_334
                    apply False.elim assump_132
            case inr assump_103 =>
              cases assump_91
              case inl assump_140 =>
                have assump_335 : (p0 ∨ p3) := by
                  apply Or.inl
                  exact assump_84
                let assump_147 := assump_93 assump_335
                apply False.elim assump_147
              case inr assump_141 =>
                cases assump_141
                case intro assump_151 assump_152 =>
                  cases assump_152
                  case intro assump_155 assump_156 =>
                    have assump_336 : (p0 ∨ p3) := by
                      apply Or.inl
                      exact assump_84
                    let assump_164 := assump_93 assump_336
                    apply False.elim assump_164
  intro assump_168
  cases assump_168
  case inl assump_169 =>
    cases assump_1
    case intro assump_173 assump_174 =>
      cases assump_173
      case intro assump_175 assump_176 =>
        cases assump_175
        case intro assump_177 assump_178 =>
          cases assump_177
          case intro assump_179 assump_180 =>
            cases assump_178
            case inl assump_185 =>
              cases assump_174
              case inl assump_191 =>
                have assump_337 : (p0 ∨ p3) := by
                  apply Or.inr
                  exact assump_179
                let assump_198 := assump_176 assump_337
                apply False.elim assump_198
              case inr assump_192 =>
                cases assump_192
                case intro assump_202 assump_203 =>
                  cases assump_203
                  case intro assump_206 assump_207 =>
                    have assump_338 : p1 := by
                      exact assump_169
                    let assump_214 := assump_202 assump_338
                    apply False.elim assump_214
            case inr assump_186 =>
              cases assump_174
              case inl assump_222 =>
                have assump_339 : (p0 ∨ p3) := by
                  apply Or.inr
                  exact assump_186
                let assump_229 := assump_176 assump_339
                apply False.elim assump_229
              case inr assump_223 =>
                cases assump_223
                case intro assump_233 assump_234 =>
                  cases assump_234
                  case intro assump_237 assump_238 =>
                    have assump_340 : p1 := by
                      exact assump_169
                    let assump_245 := assump_233 assump_340
                    apply False.elim assump_245
  case inr assump_170 =>
    cases assump_1
    case intro assump_251 assump_252 =>
      cases assump_251
      case intro assump_253 assump_254 =>
        cases assump_253
        case intro assump_255 assump_256 =>
          cases assump_255
          case intro assump_257 assump_258 =>
            cases assump_256
            case inl assump_263 =>
              cases assump_252
              case inl assump_269 =>
                have assump_341 : (p0 ∨ p3) := by
                  apply Or.inr
                  exact assump_257
                let assump_276 := assump_254 assump_341
                apply False.elim assump_276
              case inr assump_270 =>
                cases assump_270
                case intro assump_280 assump_281 =>
                  cases assump_281
                  case intro assump_284 assump_285 =>
                    have assump_342 : (p0 ∨ p3) := by
                      apply Or.inr
                      exact assump_284
                    let assump_293 := assump_254 assump_342
                    apply False.elim assump_293
            case inr assump_264 =>
              cases assump_252
              case inl assump_301 =>
                have assump_343 : (p0 ∨ p3) := by
                  apply Or.inr
                  exact assump_264
                let assump_308 := assump_254 assump_343
                apply False.elim assump_308
              case inr assump_302 =>
                cases assump_302
                case intro assump_312 assump_313 =>
                  cases assump_313
                  case intro assump_316 assump_317 =>
                    have assump_344 : (p0 ∨ p3) := by
                      apply Or.inr
                      exact assump_316
                    let assump_325 := assump_254 assump_344
                    apply False.elim assump_325


variable (p0 p5 p6 p4 p3 p1 p2 : Prop)
theorem file33_85450 : (((((False ∨ p3) → (p5 ∨ p1)) → ((True ∨ p5) → (p2 → p4))) → (((p2 ∨ p1) → False) ∨ ((p0 ∧ p6) → False))) → ((((p2 → p3) → (False → p3)) ∨ ((p6 → False) → False)) ∨ (((p6 ∧ p4) ∨ (p6 ∧ p6)) → ((p1 ∧ p0) → (p0 → p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p1 p5 p2 p3 p6 p0 p4 : Prop)
theorem file33_85847 : (((((True → False) → (p4 → False)) → False) → (((True ∧ p0) → (p0 → False)) ∧ ((True ∧ p1) → (p3 ∨ True)))) ∧ ((((p5 ∧ p1) ∨ (p5 ∨ p5)) → ((p5 ∨ p5) ∨ (p4 ∨ p1))) ∨ (((True ∧ p0) → (p2 ∨ p6)) → False))) := by
  apply And.intro
  intro assump_19
  apply And.intro
  intro assump_20
  intro assump_21
  cases assump_20
  case intro assump_24 assump_25 =>
    have assump_70 : ((True → False) → (p4 → False)) := by
      intro assump_33
      intro assump_34
      have assump_71 : True := by
        apply True.intro
      let assump_39 := assump_33 assump_71
      apply False.elim assump_39
    let assump_32 := assump_19 assump_70
    apply False.elim assump_32
  intro assump_46
  cases assump_46
  case intro assump_47 assump_48 =>
    apply Or.inr
    apply True.intro
  apply Or.inl
  intro assump_55
  cases assump_55
  case inl assump_56 =>
    cases assump_56
    case intro assump_58 assump_59 =>
      apply Or.inl
      apply Or.inl
      exact assump_58
  case inr assump_57 =>
    cases assump_57
    case inl assump_64 =>
      apply Or.inl
      apply Or.inl
      exact assump_64
    case inr assump_65 =>
      apply Or.inl
      apply Or.inl
      exact assump_65


variable (p1 p5 p2 p0 p7 p3 : Prop)
theorem file33_87089 : (((((p5 ∧ p2) ∨ (p3 → False)) ∨ ((p2 → p7) → False)) ∧ (((p5 ∨ False) ∧ (p3 → False)) ∧ ((p1 → p0) ∧ (p5 → False)))) → False) := by
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
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_15
                case intro assump_24 assump_25 =>
                  have assump_84 : p5 := by
                    exact assump_18
                  let assump_30 := assump_25 assump_84
                  apply False.elim assump_30
              case inr assump_19 =>
                apply False.elim assump_19
      case inr assump_7 =>
        cases assump_3
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            cases assump_40
            case inl assump_42 =>
              cases assump_39
              case intro assump_48 assump_49 =>
                have assump_85 : p5 := by
                  exact assump_42
                let assump_54 := assump_49 assump_85
                apply False.elim assump_54
            case inr assump_43 =>
              apply False.elim assump_43
    case inr assump_5 =>
      cases assump_3
      case intro assump_62 assump_63 =>
        cases assump_62
        case intro assump_64 assump_65 =>
          cases assump_64
          case inl assump_66 =>
            cases assump_63
            case intro assump_72 assump_73 =>
              have assump_86 : p5 := by
                exact assump_66
              let assump_78 := assump_73 assump_86
              apply False.elim assump_78
          case inr assump_67 =>
            apply False.elim assump_67


variable (p5 p4 p3 p6 p0 p7 p2 : Prop)
theorem file33_89125 : ((((((p0 → p7) ∨ (p2 ∨ p5)) ∧ ((True → False) → (p7 → False))) → (((p7 ∨ p5) → False) → ((p6 ∧ p3) ∧ (p0 → False)))) ∧ ((((p4 ∨ p3) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_44 : (((p4 ∨ p3) ∧ (True → False)) → False) := by
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          have assump_45 : True := by
            apply True.intro
          let assump_29 := assump_22 assump_45
          apply False.elim assump_29
        case inr assump_24 =>
          have assump_46 : True := by
            apply True.intro
          let assump_37 := assump_22 assump_46
          apply False.elim assump_37
    let assump_19 := assump_14 assump_44
    apply False.elim assump_19


variable (p2 p1 p4 p0 p6 p5 : Prop)
theorem file33_90049 : ((((((False ∨ p1) ∧ (p1 ∧ p5)) → ((p2 → False) → False)) ∧ (((p1 → p2) → (p6 → p4)) ∧ ((p2 → p5) → False))) ∧ ((((p1 → False) → (p6 ∧ False)) ∧ ((p0 → True) → False)) ∨ (((False ∧ p5) ∧ (p1 → p4)) ∧ ((p1 ∨ False) ∧ (p6 → p4))))) → False) := by
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
            have assump_35 : (p0 → True) := by
              intro assump_23
              apply True.intro
            let assump_22 := assump_17 assump_35
            apply False.elim assump_22
        case inr assump_15 =>
          cases assump_15
          case intro assump_27 assump_28 =>
            cases assump_27
            case intro assump_29 assump_30 =>
              cases assump_29
              case intro assump_31 assump_32 =>
                apply False.elim assump_31


variable (p4 p2 p6 p7 p5 p1 p0 p3 : Prop)
theorem file33_91155 : (((((p4 ∧ False) → False) ∨ ((p2 → False) ∧ (p5 ∨ p3))) → (((False → False) ∨ (p3 → p7)) ∨ ((False → p2) → (p1 → False)))) ∨ ((((p2 ∨ p3) ∨ (p6 ∧ p6)) ∨ ((p6 ∧ p0) ∨ (p5 → p1))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        apply Or.inl
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      case inr assump_14 =>
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply False.elim assump_22


variable (p7 p4 p2 p6 p0 p3 : Prop)
theorem file33_91923 : (((((p4 → p2) ∧ (False ∨ False)) ∧ ((p7 → False) ∨ (p0 → False))) → (((p6 → False) → False) ∧ ((p7 ∨ p7) ∨ (p0 ∨ p7)))) ∨ ((((p0 ∨ False) ∧ (p7 ∨ p7)) ∧ ((False ∨ True) ∧ (p3 ∨ p3))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        apply False.elim assump_12
  cases assump_1
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case inl assump_23 =>
        apply False.elim assump_23
      case inr assump_24 =>
        apply False.elim assump_24


variable (p0 p1 p2 p4 p7 p5 p3 : Prop)
theorem file33_92764 : (((((p7 ∨ False) → (p3 → p4)) → ((p5 ∧ p3) ∨ (p7 ∧ False))) → (((p1 ∨ p4) ∧ (p7 ∨ p2)) → False)) → ((((False ∨ p0) ∨ (p2 → p2)) ∨ ((p1 ∧ True) ∨ (p3 ∧ True))) ∨ (((p0 ∨ p5) → (p3 ∨ False)) → False))) := by
  intro assump_7
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_10
  exact assump_10


variable (p1 p6 p4 p5 p3 p7 p2 p0 : Prop)
theorem file33_93134 : (((((p1 → False) ∧ (p0 → False)) ∧ ((False → p7) ∨ (p4 → False))) ∧ (((p6 ∧ p7) ∨ (p5 → False)) ∧ ((True ∨ False) → False))) → ((((p3 ∧ p5) ∧ (True ∨ p1)) → ((p6 → p6) → False)) ∧ (((p2 → p2) ∨ (False → True)) ∧ ((p3 → False) → (False → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case inl assump_14 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_21
              case inl assump_28 =>
                cases assump_19
                case intro assump_32 assump_33 =>
                  cases assump_32
                  case inl assump_34 =>
                    cases assump_34
                    case intro assump_36 assump_37 =>
                      have assump_212 : (True ∨ False) := by
                        apply Or.inl
                        apply True.intro
                      let assump_44 := assump_33 assump_212
                      apply False.elim assump_44
                  case inr assump_35 =>
                    have assump_213 : (True ∨ False) := by
                      apply Or.inl
                      apply True.intro
                    let assump_52 := assump_33 assump_213
                    apply False.elim assump_52
              case inr assump_29 =>
                cases assump_19
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case inl assump_60 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      have assump_214 : (True ∨ False) := by
                        apply Or.inl
                        apply True.intro
                      let assump_70 := assump_59 assump_214
                      apply False.elim assump_70
                  case inr assump_61 =>
                    have assump_215 : (True ∨ False) := by
                      apply Or.inl
                      apply True.intro
                    let assump_78 := assump_59 assump_215
                    apply False.elim assump_78
      case inr assump_15 =>
        cases assump_1
        case intro assump_84 assump_85 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              cases assump_87
              case inl assump_94 =>
                cases assump_85
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case inl assump_100 =>
                    cases assump_100
                    case intro assump_102 assump_103 =>
                      have assump_216 : (True ∨ False) := by
                        apply Or.inl
                        apply True.intro
                      let assump_110 := assump_99 assump_216
                      apply False.elim assump_110
                  case inr assump_101 =>
                    have assump_217 : (True ∨ False) := by
                      apply Or.inl
                      apply True.intro
                    let assump_118 := assump_99 assump_217
                    apply False.elim assump_118
              case inr assump_95 =>
                cases assump_85
                case intro assump_124 assump_125 =>
                  cases assump_124
                  case inl assump_126 =>
                    cases assump_126
                    case intro assump_128 assump_129 =>
                      have assump_218 : (True ∨ False) := by
                        apply Or.inl
                        apply True.intro
                      let assump_136 := assump_125 assump_218
                      apply False.elim assump_136
                  case inr assump_127 =>
                    have assump_219 : (True ∨ False) := by
                      apply Or.inl
                      apply True.intro
                    let assump_144 := assump_125 assump_219
                    apply False.elim assump_144
  apply And.intro
  cases assump_1
  case intro assump_148 assump_149 =>
    cases assump_148
    case intro assump_150 assump_151 =>
      cases assump_150
      case intro assump_152 assump_153 =>
        cases assump_151
        case inl assump_158 =>
          cases assump_149
          case intro assump_162 assump_163 =>
            cases assump_162
            case inl assump_164 =>
              cases assump_164
              case intro assump_166 assump_167 =>
                apply Or.inl
                intro assump_174
                exact assump_174
            case inr assump_165 =>
              apply Or.inl
              intro assump_181
              exact assump_181
        case inr assump_159 =>
          cases assump_149
          case intro assump_186 assump_187 =>
            cases assump_186
            case inl assump_188 =>
              cases assump_188
              case intro assump_190 assump_191 =>
                apply Or.inl
                intro assump_198
                exact assump_198
            case inr assump_189 =>
              apply Or.inl
              intro assump_205
              exact assump_205
  intro assump_208
  intro assump_209
  apply False.elim assump_209


variable (p3 p5 p1 p2 p0 p7 p6 : Prop)
theorem file33_98664 : (((((p0 → True) → False) → ((False ∧ p1) ∧ (p7 ∧ p2))) → False) → ((((p5 → p3) ∧ (p2 → p6)) ∧ ((p2 → p7) ∧ (p1 ∧ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          have assump_51 : (((p0 → True) → False) → ((False ∧ p1) ∧ (p7 ∧ p2))) := by
            intro assump_24
            apply And.intro
            apply And.intro
            have assump_52 : (p0 → True) := by
              intro assump_28
              apply True.intro
            let assump_27 := assump_24 assump_52
            apply False.elim assump_27
            exact assump_15
            apply And.intro
            have assump_53 : (p0 → True) := by
              intro assump_37
              apply True.intro
            let assump_36 := assump_24 assump_53
            apply False.elim assump_36
            have assump_54 : (p0 → True) := by
              intro assump_44
              apply True.intro
            let assump_43 := assump_24 assump_54
            apply False.elim assump_43
          let assump_23 := assump_1 assump_51
          apply False.elim assump_23


variable (p1 p7 p6 p2 p0 : Prop)
theorem file33_100020 : (((((p0 ∨ True) ∧ (p1 ∧ p2)) ∨ ((p6 ∨ p0) ∧ (p1 ∧ p2))) ∧ (((p7 ∧ p2) ∨ (p0 → True)) → False)) → ((((p2 → p1) ∧ (True → False)) → ((True → False) ∨ (p0 ∨ True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case intro assump_15 assump_16 =>
            have assump_77 : ((p7 ∧ p2) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_24
              apply True.intro
            let assump_23 := assump_6 assump_77
            apply False.elim assump_23
        case inr assump_12 =>
          cases assump_10
          case intro assump_30 assump_31 =>
            have assump_78 : ((p7 ∧ p2) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_39
              apply True.intro
            let assump_38 := assump_6 assump_78
            apply False.elim assump_38
    case inr assump_8 =>
      cases assump_8
      case intro assump_43 assump_44 =>
        cases assump_43
        case inl assump_45 =>
          cases assump_44
          case intro assump_49 assump_50 =>
            have assump_79 : ((p7 ∧ p2) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_58
              apply True.intro
            let assump_57 := assump_6 assump_79
            apply False.elim assump_57
        case inr assump_46 =>
          cases assump_44
          case intro assump_64 assump_65 =>
            have assump_80 : ((p7 ∧ p2) ∨ (p0 → True)) := by
              apply Or.inr
              intro assump_73
              apply True.intro
            let assump_72 := assump_6 assump_80
            apply False.elim assump_72


variable (p4 p6 p5 p3 p0 p2 p1 : Prop)
theorem file33_101927 : (((((p0 ∨ True) → False) → ((p3 ∨ p4) → (p0 ∨ p2))) → False) → ((((p1 ∨ p1) ∨ (p6 → p1)) → False) → (((p5 ∨ False) → (p1 → False)) ∨ ((p3 ∧ p3) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  cases assump_7
  case inl assump_11 =>
    have assump_43 : (((p0 ∨ True) → False) → ((p3 ∨ p4) → (p0 ∨ p2))) := by
      intro assump_18
      intro assump_19
      cases assump_19
      case inl assump_20 =>
        have assump_44 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_26 := assump_18 assump_44
        apply False.elim assump_26
      case inr assump_21 =>
        have assump_45 : (p0 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_34 := assump_18 assump_45
        apply False.elim assump_34
    let assump_17 := assump_1 assump_43
    apply False.elim assump_17
  case inr assump_12 =>
    apply False.elim assump_12


variable (p0 p4 p1 : Prop)
theorem file33_102935 : (((((p0 → False) → (p0 → False)) ∨ ((p4 ∧ p4) ∧ (p1 → p0))) → False) → False) := by
  intro assump_7
  have assump_24 : (((p0 → False) → (p0 → False)) ∨ ((p4 ∧ p4) ∧ (p1 → p0))) := by
    apply Or.inl
    intro assump_11
    intro assump_12
    have assump_25 : p0 := by
      exact assump_12
    let assump_17 := assump_11 assump_25
    apply False.elim assump_17
  let assump_10 := assump_7 assump_24
  apply False.elim assump_10


variable (p1 p3 p5 p6 p2 : Prop)
theorem file33_103424 : ((((((p2 → p6) → (p2 → True)) → ((False ∧ p1) → (p2 → p5))) ∨ (((p1 ∨ False) → (p6 → False)) ∨ ((p6 → False) ∧ (p2 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p2 → p6) → (p2 → True)) → ((False ∧ p1) → (p2 → p5))) ∨ (((p1 ∨ False) → (p6 → False)) ∨ ((p6 → False) ∧ (p2 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p3 p6 p7 p5 p0 p2 p1 : Prop)
theorem file33_104031 : (((((p1 ∨ True) ∧ (True ∨ p0)) → ((p6 ∨ p6) → (p2 → p7))) → (((p3 → p0) ∧ (p5 ∧ False)) → False)) ∧ ((((p0 ∨ p2) → (True ∧ True)) → ((True ∧ p3) ∨ (p7 → p5))) → (((p4 ∧ True) ∧ (p7 ∨ p5)) ∨ ((p1 → False) → (True ∨ p7))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  intro assump_13
  apply Or.inr
  intro assump_16
  apply Or.inl
  apply True.intro


variable (p4 p7 p5 p0 p3 p6 p2 p1 : Prop)
theorem file33_104600 : (((((False ∧ p5) → (p1 ∧ p2)) → ((p6 ∧ False) ∧ (p0 → False))) → False) ∨ ((((p7 ∧ p7) → False) ∧ ((p0 → False) → False)) ∨ (((p3 → p1) ∨ (p4 → p0)) → ((True → False) ∧ (p3 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_20 : ((False ∧ p5) → (p1 ∧ p2)) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_20
  let assump_14 := And.left assump_4
  let assump_15 := And.right assump_14
  apply False.elim assump_15


variable (p7 p2 p5 p3 p1 : Prop)
theorem file33_105291 : (((((p3 → False) → (p2 ∧ p7)) ∧ ((p1 → False) ∧ (False ∧ p3))) ∧ (((p5 ∨ p1) ∧ (p1 ∧ p3)) ∨ ((False ∧ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p6 p1 p0 p2 p4 p7 p3 p5 : Prop)
theorem file33_105773 : (((((False ∧ p7) → (p3 → False)) ∨ ((False ∧ p4) ∨ (p4 → False))) → (((p5 → p2) ∨ (p3 ∧ p6)) → ((p4 → True) ∨ (p3 ∨ p2)))) ∨ ((((p1 ∧ p0) → False) ∨ ((p7 → False) → False)) ∨ (((p7 ∧ p5) ∨ (p2 ∧ p0)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case inl assump_12 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      case inr assump_13 =>
        apply Or.inl
        intro assump_20
        apply True.intro
  case inr assump_4 =>
    cases assump_4
    case intro assump_21 assump_22 =>
      cases assump_1
      case inl assump_27 =>
        apply Or.inl
        intro assump_31
        apply True.intro
      case inr assump_28 =>
        cases assump_28
        case inl assump_32 =>
          cases assump_32
          case intro assump_34 assump_35 =>
            apply False.elim assump_34
        case inr assump_33 =>
          apply Or.inl
          intro assump_40
          apply True.intro


variable (p7 p2 p6 p4 p1 p3 : Prop)
theorem file33_107018 : (((((p4 → p7) ∨ (True → p6)) → ((p6 ∨ False) ∧ (p1 → False))) ∧ (((p2 → True) ∨ (p3 ∨ p2)) → False)) → ((((p1 → False) ∨ (p1 ∨ p6)) → ((True → False) ∧ (True ∧ p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : ((p2 → True) ∨ (p3 ∨ p2)) := by
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_11 := assump_6 assump_16
    apply False.elim assump_11


variable (p1 p6 p0 p2 p4 p3 p7 : Prop)
theorem file33_107536 : ((((((p4 ∧ False) → (p7 ∨ p4)) → False) ∧ (((p4 ∧ p1) → (p2 → p2)) ∧ ((p2 → False) → (p3 → p2)))) ∧ ((((p0 ∨ False) ∧ (True → False)) ∨ ((p6 ∨ p4) ∨ (p6 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_28 : (((p0 ∨ False) ∧ (True → False)) ∨ ((p6 ∨ p4) ∨ (p6 → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_17
          have assump_29 : (((p0 ∨ False) ∧ (True → False)) ∨ ((p6 ∨ p4) ∨ (p6 → False))) := by
            apply Or.inr
            apply Or.inl
            apply Or.inl
            exact assump_17
          let assump_21 := assump_3 assump_29
          apply False.elim assump_21
        let assump_16 := assump_3 assump_28
        apply False.elim assump_16


variable (p3 p7 p5 p2 p4 p6 p1 : Prop)
theorem file33_108497 : ((((((True ∧ True) ∧ (p7 ∧ False)) ∧ ((p1 ∧ p4) ∧ (p4 → False))) ∧ (((True → p7) → (p4 → False)) ∨ ((p3 → False) → (False ∧ p4)))) ∧ ((((p3 → False) ∨ (True → False)) ∧ ((True ∧ p6) ∨ (p1 → p4))) ∨ (((p2 ∧ True) ∨ (False ∧ p5)) → ((p7 → True) → (True ∧ p3))))) → False) := by
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
            case intro assump_16 assump_17 =>
              apply False.elim assump_17


variable (p1 p7 p0 p6 p4 p5 p2 : Prop)
theorem file33_109264 : (((((p7 → False) ∧ (False ∧ p7)) → False) ∨ (((p7 ∨ p7) ∧ (p6 ∨ False)) → False)) ∨ ((((p4 ∨ p5) → False) ∧ ((p5 → False) → (p2 ∨ p1))) → (((p2 ∧ True) ∨ (True ∨ p0)) ∧ ((True ∨ p6) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p4 p1 p0 p5 : Prop)
theorem file33_109703 : ((((((p5 ∧ False) ∧ (p5 ∧ p5)) → False) ∨ (((p0 ∨ p4) → False) ∧ ((p0 → p1) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p5 ∧ False) ∧ (p5 ∧ p5)) → False) ∨ (((p0 ∨ p4) → False) ∧ ((p0 → p1) ∨ (True → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p1 p4 p3 p5 p2 p6 : Prop)
theorem file33_110271 : (((((p7 ∧ p5) ∨ (p2 ∧ p2)) ∨ ((p3 → False) ∧ (p4 ∨ p3))) → False) → ((((p2 → False) ∧ (p1 ∧ p7)) → ((p1 → False) → (p7 ∧ p4))) ∨ (((p4 ∧ p6) → False) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      exact assump_13
  cases assump_4
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      have assump_37 : p1 := by
        exact assump_24
      let assump_33 := assump_5 assump_37
      apply False.elim assump_33


variable (p7 p3 p1 p4 p6 p2 p0 : Prop)
theorem file33_110957 : (((((p4 ∨ p2) → False) → ((True → False) → (p6 → False))) ∨ (((p0 ∧ p7) ∧ (p7 ∨ p4)) ∧ ((p7 ∧ True) ∨ (p3 → False)))) ∨ ((((p3 → p0) → False) → ((p2 ∧ True) ∧ (p4 → False))) ∨ (((p1 → False) → (p1 → p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  have assump_23 : True := by
    apply True.intro
  let assump_19 := assump_10 assump_23
  apply False.elim assump_19


variable (p3 p6 p0 p2 p5 : Prop)
theorem file33_111437 : ((((((p5 ∨ p3) → (p6 ∨ p6)) → ((False → False) ∧ (False → False))) ∨ (((False → False) → False) → ((p2 ∧ p0) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p5 ∨ p3) → (p6 ∨ p6)) → ((False → False) ∧ (False → False))) ∨ (((False → False) → False) → ((p2 ∧ p0) → (p0 → False)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    apply False.elim assump_9
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p6 p4 p3 p7 : Prop)
theorem file33_112031 : ((((((p3 → False) → (p4 → p0)) ∧ ((p7 → False) ∧ (False ∨ p4))) → (((p6 → False) → False) → ((False → False) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p3 → False) → (p4 → p0)) ∧ ((p7 → False) ∧ (False ∨ p4))) → (((p6 → False) → False) → ((False → False) ∨ (p6 → False)))) := by
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
          apply Or.inl
          intro assump_23
          apply False.elim assump_23
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p3 p2 p1 p5 p0 p4 p6 : Prop)
theorem file33_112840 : (((((p0 → False) ∨ (p2 ∨ p1)) → ((p2 → p5) ∧ (True → p4))) ∧ (((p6 ∨ p2) ∨ (p6 → p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((p6 ∨ p2) ∨ (p6 → p3)) := by
      apply Or.inr
      intro assump_9
      have assump_21 : ((p6 ∨ p2) ∨ (p6 → p3)) := by
        apply Or.inl
        apply Or.inl
        exact assump_9
      let assump_13 := assump_3 assump_21
      apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


