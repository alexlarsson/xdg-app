# Source library for shell script tests
#
# Copyright (C) 2016 Alexander Larsson <alexl@redhat.com>
# Copyright (C) 2011 Colin Walters <walters@verbum.org>
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2 of the License, or (at your option) any later version.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the
# Free Software Foundation, Inc., 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.

if [ -n "${G_TEST_SRCDIR:-}" ]; then
  test_srcdir="${G_TEST_SRCDIR}"
else
  test_srcdir=$(dirname $0)
fi

if [ -n "${G_TEST_BUILDDIR:-}" ]; then
  test_builddir="${G_TEST_BUILDDIR}"
else
  test_builddir=$(dirname $0)
fi

assert_not_reached () {
    echo $@ 1>&2; exit 1
}

test_tmpdir=$(pwd)

# Sanity check that we're in a tmpdir that has
# just .testtmp (created by tap-driver for `make check`,
# or nothing at all (as ginstest-runner does)
if ! test -f .testtmp; then
    files=$(ls)
    if test -n "${files}"; then
	ls -l
	assert_not_reached "test tmpdir=${test_tmpdir} is not empty; run this test via \`make check TESTS=\`, not directly"
    fi
    # Remember that this is an acceptable test $(pwd), for the benefit of
    # C and JS tests which may source this file again
    touch .testtmp
fi

export G_DEBUG=fatal-warnings

# Also, unbreak `tar` inside `make check`...Automake will inject
# TAR_OPTIONS: --owner=0 --group=0 --numeric-owner presumably so that
# tarballs are predictable, except we don't want this in our tests.
unset TAR_OPTIONS

if test -n "${OT_TESTS_DEBUG:-}"; then
    set -x
fi

if test -n "${OT_TESTS_VALGRIND:-}"; then
    CMD_PREFIX="env G_SLICE=always-malloc valgrind -q --leak-check=full --num-callers=30 --suppressions=${test_srcdir}/flatpak-valgrind.supp"
else
    CMD_PREFIX=""
fi

# We need this to be in /var/tmp because /tmp has no xattr support
TEST_DATA_DIR=`mktemp -d /var/tmp/test-flatpak-XXXXXX`

export XDG_DATA_HOME=${TEST_DATA_DIR}/share

export USERDIR=${TEST_DATA_DIR}/share/flatpak
export ARCH=`flatpak --default-arch`

export FLATPAK="${CMD_PREFIX} flatpak"

assert_streq () {
    test "$1" = "$2" || (echo 1>&2 "$1 != $2"; exit 1)
}

assert_not_streq () {
    (! test "$1" = "$2") || (echo 1>&2 "$1 == $2"; exit 1)
}

assert_has_file () {
    test -f "$1" || (echo 1>&2 "Couldn't find '$1'"; exit 1)
}

assert_has_symlink () {
    test -L "$1" || (echo 1>&2 "Couldn't find '$1'"; exit 1)
}

assert_has_dir () {
    test -d "$1" || (echo 1>&2 "Couldn't find '$1'"; exit 1)
}

assert_not_has_file () {
    if test -f "$1"; then
        sed -e 's/^/# /' < "$1" >&2
        echo 1>&2 "File '$1' exists"
        exit 1
    fi
}

assert_not_file_has_content () {
    if grep -q -e "$2" "$1"; then
        sed -e 's/^/# /' < "$1" >&2
        echo 1>&2 "File '$1' incorrectly matches regexp '$2'"
        exit 1
    fi
}

assert_not_has_dir () {
    if test -d "$1"; then
	echo 1>&2 "Directory '$1' exists"; exit 1
    fi
}

assert_file_has_content () {
    if ! grep -q -e "$2" "$1"; then
        sed -e 's/^/# /' < "$1" >&2
        echo 1>&2 "File '$1' doesn't match regexp '$2'"
        exit 1
    fi
}

assert_symlink_has_content () {
    if ! readlink "$1" | grep -q -e "$2"; then
        readlink "$1" |sed -e 's/^/# /' >&2
        echo 1>&2 "Symlink '$1' doesn't match regexp '$2'"
        exit 1
    fi
}

assert_file_empty() {
    if test -s "$1"; then
        sed -e 's/^/# /' < "$1" >&2
        echo 1>&2 "File '$1' is not empty"
        exit 1
    fi
}

setup_repo () {
    . $(dirname $0)/make-test-runtime.sh org.test.Platform bash ls cat echo readlink > /dev/null
    . $(dirname $0)/make-test-app.sh > /dev/null
    flatpak remote-add --user --no-gpg-verify test-repo repo
}

setup_sdk_repo () {
    . $(dirname $0)/make-test-runtime.sh org.test.Sdk bash ls cat echo readlink make mkdir cp touch > /dev/null
}


install_repo () {
    ${FLATPAK} --user install test-repo org.test.Platform master
    ${FLATPAK} --user install test-repo org.test.Hello master
}

install_sdk_repo () {
    ${FLATPAK} --user install test-repo org.test.Sdk master
}

run () {
    ${CMD_PREFIX} flatpak run "$@"

}

run_sh () {
    ${CMD_PREFIX} flatpak run --command=bash ${ARGS-} org.test.Hello -c "$*"
}

skip_without_bwrap () {
    if [ -z "${FLATPAK_BWRAP:-}" ]; then
        # running installed-tests: assume we know what we're doing
        :
    elif ! "$FLATPAK_BWRAP" --ro-bind / / /bin/true > bwrap-result 2>&1; then
        sed -e 's/^/# /' < bwrap-result
        echo "1..0 # SKIP Cannot run bwrap"
        exit 0
    fi
}

sed s#@testdir@#${test_builddir}# ${test_srcdir}/session.conf.in > session.conf
eval `dbus-launch --config-file=session.conf --sh-syntax`

trap "rm -rf $TEST_DATA_DIR; /bin/kill $DBUS_SESSION_BUS_PID" EXIT
