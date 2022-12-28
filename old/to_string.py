def to_string(t):
    match t["tag"]:
        case "var":
            return t["name"]
        case "star":
            return "*"
        case "sort":
            return "@"
        case "app":
            children = t["children"]
            return f"%({to_string(children[0])})({to_string(children[1])})"
        case "const":
            children = t["children"]
            if len(children) == 0:
                children_str = ""
            else:
                children_str = children[0]
                for child in children[1:]:
                    children_str += ",(" + to_string(child) + ")"
            # (M1),(M2),...,(Mn)
            return f"{t['op']}[{children_str}]"
        case "lambda":
            children = t["children"]
            return f"${t['var']}:({to_string(children[0])}).({to_string(children[1])})"
        case "type":
            children = t["children"]
            return f"Pai {t['var']}:({to_string(children[0])}).({to_string(children[1])})"
