from asyncio import subprocess
from subprocess import run
import re, sys, os

log_off_env = os.environ.copy()
log_off_env["RUST_LOG"] = "off"
log_file = "Gillian-Rust/file.log"


def compile(example_file):
    if len(sys.argv) >= 3 and sys.argv[2] == "--mir":
        env = os.environ
    else:
        env = log_off_env
    run(
        ["cargo", "run", "--", "--out-dir", "output", example_file],
        env=env,
    )


def gillian_rust(gil_file):
    run(
        [
            "esy",
            "x",
            "gillian-rust",
            "exec",
            "-R",
            "../runtime",
            "-a",
            f"../{gil_file}",
        ],
        cwd="Gillian-Rust",
        stdout=subprocess.DEVNULL,
    )


def expected_result(example_file):
    with open(example_file, "r") as f:
        for line in f.readlines():
            m = line.find("ENDSWITH: ")
            if m > 0:
                return line[m + 10 :].strip()


def obtained_result(log):
    with open(log, "r") as f:
        s = reversed(f.readlines())
    p = re.compile(r"\(ret: (.*)\)")
    for i in s:
        match = p.search(i)
        if match is not None:
            return match.group(1).strip()


def test(name):
    example_file = f"examples/{name}.rs"
    compile(example_file)
    gillian_rust(f"output/{name}.gil")
    expected = expected_result(example_file)
    actual = obtained_result(log_file)
    return None if expected == actual else (expected, actual)


if __name__ == "__main__":
    arg = sys.argv[1]
    try:
        result = test(arg)
        if result is None:
            print(f"{arg}: OK!")
        else:
            print(f"{arg}: Failure! Expected {result[0]}, got {result[1]}")
            print(f"See: {log_file}")
    except:
        print(f"{arg}: Failure! error in the test process")
        print(f"See: {log_file}")
