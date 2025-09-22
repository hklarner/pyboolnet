

import os
import platform
import logging
import subprocess

import pyboolnet
from pyboolnet import GRAPHVIZ_LAYOUT_ENGINES
from pyboolnet import find_command

log = logging.getLogger(__name__)


def check_all_dependencies():
    print(f"{'CONDA' in os.environ=}")
    print(f"{platform.system()=}")

    check_gringo_responds()
    check_clasp_responds()
    check_nusmv_responds()
    check_bnet2primes_responds()
    check_layout_engines()
    check_imagemagick_responds()
    check_espresso_responds()
    check_eqntott_responds()


def check_gringo_responds():
    cmd = find_command("gringo")
    cmd = [cmd, "--help"]
    log.info(f"gringo command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if not proc.returncode == 0:
        log.error(f"gringo did not respond with return code 0: return_code={proc.returncode}")
        return

    if "Gringo" not in out:
        log.error(f"gringo output does not contain 'Gringo': {out=}")
        return

    log.info("gringo works")


def check_clasp_responds():
    cmd = find_command("clasp")
    cmd = [cmd, "--help"]
    log.info(f"clasp command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if not proc.returncode == 0:
        log.error(f"clasp did not respond with return code 0: return_code={proc.returncode}")
        return

    if "clasp version" not in out:
        log.error(f"clasp output does not contain 'clasp version': {out=}")
        return

    log.info("clasp works")


def check_nusmv_responds():
    cmd = find_command("nusmv")
    cmd = [cmd]
    log.info(f"clasp command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate(input="MODULE main".encode())
    out = out.decode()

    if "NuSMV" not in out:
        log.error(f"NuSMV output does not contain 'NuSMV': {out=}")
        return

    log.info("NuSMV works")


def check_bnet2primes_responds():
    cmd = find_command("bnet2prime")
    cmd = [cmd, "--ver"]
    log.info(f"bnet2prime command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if not proc.returncode == 0:
        log.error(f"bnet2prime did not respond with return code 0: return_code={proc.returncode}")
        return

    if "BNetToPrime" not in out:
        log.error(f"bnet2prime output does not contain 'BNetToPrime': {out=}")
        return

    log.info("BNetToPrime works")


def check_layout_engines():
    for name in GRAPHVIZ_LAYOUT_ENGINES:
        cmd = find_command(name)
        log.info(f"{name} command = {cmd}")

        proc = subprocess.Popen([cmd, "-V"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        err = err.decode()  # for some reason graphviz" reports on stderr

        if not proc.returncode == 0:
            log.error(f"{name} did not respond with return code 0: return_code={proc.returncode}")
            return

        if "graphviz" not in err:
            log.error(f"{name} output does not contain 'graphviz': out={err}")
            return

        log.info(f"{name} works")


def check_imagemagick_responds():
    cmd = find_command("convert")
    cmd = [cmd, "-help"]
    log.info(f"imagemagick command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if "ImageMagick" not in out:
        log.error(f"imagemagick output does not contain 'ImageMagick': {out=}")
        return

    log.info(f"imagemagick works")


def check_espresso_responds():
    cmd = find_command("espresso")
    cmd = [cmd, "--help"]
    log.info(f"espresso command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if "Espresso" not in out:
        log.error(f"espresso output does not contain 'Espresso': {out=}")
        return

    log.info(f"espresso works")


def check_eqntott_responds():
    cmd = find_command("eqntott")
    cmd = [cmd, "--help"]
    log.info(f"eqntott command = {' '.join(cmd)}")

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    err = err.decode()

    if "usage" not in err:
        log.error(f"eqntott output does not contain 'usage': {out=}")
        return

    log.info(f"eqntott works")


if __name__ == '__main__':
    check_all_dependencies()
