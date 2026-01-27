import os
import re
import logging
import sys

logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger(__name__)

def _read_file_content(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        return f.read()

def _is_sv_or_v_file(filename):
    return filename.lower().endswith(('.sv', '.v'))

def _get_files_from_directory(directory, recursive=False):
    files = []
    if recursive:
        for root, _, filenames in os.walk(directory):
            for filename in filenames:
                if _is_sv_or_v_file(filename):
                    files.append(os.path.join(root, filename))
    else:
        for filename in os.listdir(directory):
            full_path = os.path.join(directory, filename)
            if os.path.isfile(full_path) and _is_sv_or_v_file(filename):
                files.append(full_path)
    return files


def fv_files_creation(storage, output_dir):
    for path, content in storage.items():
        logger.info(f"\nArchivo: {path}")
        lines = content.splitlines()
        input_lines = []
        module_name = None
        for line in lines:
            stripped_line = line.strip()
            if stripped_line.startswith("//"):
                continue
            code_line = line.split("//")[0]

            module_match = re.match(r'\s*module\s+(\w+)\s*(?:#\s*\((.*?)\))?', code_line, re.S)
            if module_match:
                module_name = module_match.group(1)
                module_params = module_match.group(2)
                if module_params:
                    logger.info(f"module {module_name} #({module_params}) (")
                    input_lines.append(f"module fv_{module_name} #({module_params}) (")
                else:
                    logger.info(f"module {module_name} (")
                    input_lines.append(f"module fv_{module_name} (")
                module_match = None
            input_match = re.search(r'\binput\b(.*)', code_line)
            if input_match:
                input_line = "input" + input_match.group(1)
                logger.info(input_line)
                input_lines.append(input_line)
            output_match = re.search(r'\boutput\b(.*)', code_line)
            if output_match:
                output_line = "input" + output_match.group(1)
                logger.info(output_line)
                input_lines.append(output_line)
            endmodule_match = re.match(r'\bendmodule\b(.*)', code_line)
            if endmodule_match:
                logger.info("endmodule")
                input_lines.append(");")
                input_lines.append("  `include \"includes.svh\"")
                input_lines.append("  // Here add yours ASSERTIONS, COVERAGE, ASSUMPTIONS, etc.")
                input_lines.append("  ")
                input_lines.append("endmodule")
                input_lines.append("")
                input_lines.append(f"bind {module_name} fv_{module_name} fv_{module_name}_i(.*);")
                input_lines.append("")

        base_filename = "fv_" + os.path.splitext(os.path.basename(path))[0] + ".sv"
        if output_dir:
            new_filename = os.path.join(output_dir, base_filename)
        else:
            new_filename =  "fv_" + os.path.splitext(path)[0] + ".sv"
        try:
            os.makedirs(os.path.dirname(new_filename), exist_ok=True)
            with open(new_filename, 'w', encoding='utf-8') as f:
                for input_line in input_lines:
                    f.write(input_line + '\n')
            logger.info(f"Archivo de inputs creado: {new_filename}")
        except Exception:
            logger.exception(f"No se pudo crear el archivo {new_filename}")
            return 1
    return 0

def macros_creation(output_dir):
    svh_content = (
        "`define AST(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \\\n"
        "``block``_ast_``name``: assert property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);\n\n"
        "`define ASM(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \\\n"
        "``block``_ast_``name``: assume property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);\n\n"
        "`define COV(block=rca, name=no_name, precond=1'b1 |->, consq=1'b0) \\\n"
        "``block``_ast_``name``: cover property (@(posedge clk) disable iff(!arst_n) ``precond`` ``consq``);\n"
    )
    svh_path = os.path.join(output_dir if output_dir else ".", "includes.svh")
    try:
        os.makedirs(os.path.dirname(svh_path), exist_ok=True)
        with open(svh_path, "w", encoding="utf-8") as f:
            f.write(svh_content)
        logger.info(f"Archivo includes.svh creado en: {svh_path}")
        return 0
    except Exception:
        logger.exception("No se pudo crear el archivo includes.svh")
        return 1

def tcl_creation(storage, output_dir):
    # Crear el archivo TCL con los paths de los archivos analizados en el formato solicitado
    tcl_lines = [
        "clear -all",
        "",
        "set sepIdx [lsearch $argv ---]",
        "if {$sepIdx == -1 || [expr {$sepIdx + 1}] >= [llength $argv]} {",
        "  puts \"-Uso: jg -tcl jg_fpv.tcl --- <nombre_top_module>\" ",
        "  exit 1",
        "}",
        "set FV_TOP [lindex $argv [expr {$sepIdx + 1}]]",
        "",
        "### add here secundary files for analysis if needed",
        "",
        "### ----------------------------------",
        ""
    ]

    # Agrupar archivos RTL y FV por directorio
    rtl_files = []
    rtl_dir = None
    for path in storage.keys():
        base = os.path.basename(path)
        dir_path = os.path.dirname(os.path.abspath(path))
        rtl_files.append(base)
        if rtl_dir is None:
            rtl_dir = dir_path

    # Popular fv_files con los archivos generados en output_dir
    fv_files = []
    if output_dir and os.path.isdir(output_dir):
        for filename in os.listdir(output_dir):
            if filename.startswith("fv_") and filename.endswith(".sv"):
                fv_files.append(filename)

    tcl_lines.append(f'set RTL_DIR "{rtl_dir.replace(os.sep, "/")}"')
    tcl_lines.append(f'set FV_DIR  "{os.path.abspath(output_dir).replace(os.sep, "/")}"')
    tcl_lines.append("")

    # Escribir foreach para RTL
    tcl_lines.append("foreach f {")
    for rtl in rtl_files:
        tcl_lines.append(f"  {rtl}")
    tcl_lines.append("} {")
    tcl_lines.append("  eval analyze -sv $RTL_DIR/$f")
    tcl_lines.append("}")
    tcl_lines.append("")

    tcl_lines.append("eval analyze -sv $FV_DIR/fv_$FV_TOP.sv")
    tcl_lines.append("")

    tcl_lines.append(f'elaborate -top $FV_TOP')
    tcl_lines.append("get_design_info")
    tcl_lines.append("")
    tcl_lines.append("clock clk")
    tcl_lines.append("reset -expression !arst_n")
    tcl_lines.append("")
    tcl_lines.append("prove -all")
    tcl_lines.append("")


    tcl_path = os.path.join(output_dir if output_dir else ".", "jg_fpv.tcl")
    try:
        with open(tcl_path, "w", encoding="utf-8") as f:
            for line in tcl_lines:
                f.write(line + "\n")
        logger.info(f"Archivo TCL creado en: {tcl_path}")
    except Exception:
        logger.exception("No se pudo crear el archivo TCL")

def main():
    storage = {}
    logger.info("Menu:")
    logger.info("1. Enter a file path")
    logger.info("2. Enter a directory path (without recursion)")
    choice = input("Choose an option (1 or 2): ").strip()
    logger.info(f"You chose option {choice}")
    if choice == '1':
        filepath = input("Enter the file path: ").strip()
        if os.path.isfile(filepath) and _is_sv_or_v_file(filepath):
            storage[filepath] = _read_file_content(filepath)
            logger.info(f"Stored content of {filepath}")
        else:
            logger.error("Invalid file path or not a .sv/.v file.")
            return 3
    elif choice == '2':
        dirpath = input("Enter the directory path: ").strip()
        if os.path.isdir(dirpath):
            files = _get_files_from_directory(dirpath, recursive=False)
            for file in files:
                try:
                    storage[file] = _read_file_content(file)
                    logger.info(f"Stored content of {file}")
                except Exception:
                    logger.exception(f"Could not read {file}")
                    return 3
        else:
            logger.error("Invalid directory path.")
            return 2
    else:
        logger.error("Invalid choice.")
        return 1
    
    if len(storage) == 0:
        logger.error("No valid .sv or .v files found.")
        return 4

    output_dir = input("\nEnter the directory where you want to save the result files: ").strip()
   
    ret = macros_creation(output_dir)
    if ret != 0:
        return ret
    ret = fv_files_creation(storage, output_dir)
    if ret != 0:
        return ret
    ret = tcl_creation(storage, output_dir)
    if ret != 0:
        return ret
    return 0

if __name__ == "__main__":
    sys.exit(main())