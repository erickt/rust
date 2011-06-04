import re
import pprint
from functools import partial
from itertools import chain
from optparse import make_option

import fbuild
import fbuild.record
import fbuild.target
from fbuild.path import Path
from fbuild.functools import call

# ------------------------------------------------------------------------------

class Rustc(fbuild.builders.AbstractCompilerBuilder):
    """Create a builder for the rustc executable."""

    def __init__(self, ctx, exe, cxx_builder, *,
            platform=None,
            debug=None,
            optimize=None,
            runtime_libpaths=()):
        super().__init__(ctx, src_suffix='.rs')

        self.exe = fbuild.builders.find_program(ctx, [exe or 'rustc'])
        self.cxx_builder = cxx_builder
        self.obj_suffix = fbuild.builders.platform.obj_suffix(ctx, platform)
        self.debug = debug
        self.optimize = optimize
        self.runtime_libpaths = runtime_libpaths

    def __call__(self, srcs=(),
            dst=None,
            pre_flags=(),
            debug=None,
            optimize=None,
            shared=None,
            libpaths=(),
            flags=(),
            runtime_libpaths=(),
            **kwargs):
        cmd = [self.exe]
        cmd.extend(pre_flags)

        if (debug is None and self.debug) or debug:
            cmd.append('-g')

        if (optimize is None and self.optimize) or optimize:
            cmd.append('-O')

        if shared:
            cmd.append('--shared')

        for libpath in libpaths:
            cmd.extend(('-L', libpath))

        if dst is not None:
            cmd.extend(('-o', dst))

            if srcs:
                msg2 = '{} -> {}'.format(' '.join(srcs), dst)
            else:
                msg2 = dst
        else:
            msg2 = ' '.join(srcs)

        cmd.extend(flags)
        cmd.extend(srcs)

        runtime_libpaths = list(chain(self.runtime_libpaths, runtime_libpaths))

        return self.ctx.execute(cmd,
            msg1=str(self),
            msg2=msg2,
            runtime_libpaths=runtime_libpaths,
            **kwargs)

    # --------------------------------------------------------------------------

    def uncached_compile(self, src, dst=None, *, pre_flags=(), **kwargs):
        """Compile a rust object."""

        dst = fbuild.path.Path(dst or src).replaceext(self.obj_suffix)
        dst = dst.addroot(self.ctx.buildroot)
        dst.parent.makedirs()

        self((src,),
            dst=dst,
            pre_flags=list(chain(('-c',), pre_flags)),
            color='compile',
            **kwargs)

        return dst

    @fbuild.db.cachemethod
    def compile_glue(self, dst, *, pre_flags=(), **kwargs) -> fbuild.db.DST:
        """Compile rust glue."""

        dst = fbuild.path.Path(dst).replaceext(self.obj_suffix)
        dst = dst.addroot(self.ctx.buildroot)
        dst.parent.makedirs()

        self(
            dst=dst,
            pre_flags=list(chain(('-c', '--glue'), pre_flags)),
            color='compile',
            **kwargs)

        return dst

    def uncached_link_lib(self, *args, **kwargs):
        return self.cxx_builder.link_lib(*args, **kwargs)

    def uncached_link_exe(self, *args, **kwargs):
        return self.cxx_builder.link_exe(*args, **kwargs)

    # --------------------------------------------------------------------------

    def __str__(self):
        return self.exe.name

# ------------------------------------------------------------------------------

def pre_options(parser):
    """Add our custom command line options"""

    parser.add_options([
        make_option('-g', '--debug',
            default=False,
            action='store_true',
            help='enable debugging for all stages'),
        make_option('-O', '--optimize',
            default=False,
            action='store_true',
            help='enable optimization for all stages'),
        make_option('--clangxx',
            help='specify the clang++ executable'),
        make_option('--llvm-config',
            help='specify the llvm-config script'),
    ])

# ------------------------------------------------------------------------------

@fbuild.target.register()
def configure(ctx):
    """Configure rust."""

    platform = fbuild.builders.platform.guess_platform(ctx)

    # We prefer using the clang compiler, so add it to our platform. However if
    # it doesn't exist, we'll fall back onto the system's default compiler.
    platform = platform.union(['clang', 'clang++'])

    kwargs = dict(
        platform=platform,
        arch='i386',
        optimize=ctx.options.optimize,
        debug=ctx.options.debug,
        platform_options=[
            ({'clang++'}, {
                'exe': ctx.options.clangxx,
                'requires_version': (3, 0)}),

            # We don't want '-fPIC' set.
            ({'posix'}, {
                'warnings': ['all', 'error'],
                'flags': [
                    '-fno-rtti',
                    '-fno-strict-aliasing',
                    '-fno-exceptions']})])

    cxx_static = call('fbuild.builders.cxx.guess_static', ctx, **kwargs)
    cxx_shared = call('fbuild.builders.cxx.guess_shared', ctx, **kwargs)

    llvm_config=call('fbuild.builders.llvm.LlvmConfig', ctx,
        ctx.options.llvm_config,
        requires_version=(3, '0svn'))

    return fbuild.record.Record(
        platform = platform,
        cxx_static = cxx_static,
        cxx_shared = cxx_shared,
        llvm_config = llvm_config,
        llvm_as = call('fbuild.builders.llvm.Llvm_as', ctx,
            llvm_config.bindir() / 'llvm-as'),
        llc = call('fbuild.builders.llvm.Llc', ctx,
            llvm_config.bindir() / 'llc',
            platform=platform),
    )

# ------------------------------------------------------------------------------

def build(ctx):
    """Build rust."""

    config = configure(ctx)

    # Compile the runtime.
    libs = [build_librustrt(ctx, config), build_librustllvm(ctx, config)]

    # Compile the compiler.
    build_compiler(ctx, config, libs)

# ------------------------------------------------------------------------------

def def_substitute(ctx, config, src) -> fbuild.db.DST:
    """Substitute a definition file."""

    src = Path(src)

    # We use different substitution regex patterns depending on the platform.
    if 'linux' in config.platform:
        dst = src.replace('.def.in', '.linux.def')
        patterns = [
            (r'^(.*)$', r'{\n\1\n}', re.DOTALL),
            (r'(.+)$', r'\1;')]
    elif 'darwin' in config.platform:
        dst = src.replace('.def.in', '.darwin.def')
        patterns = [(r'^(.+)$', r'_\1')]
    elif 'windows' in platform:
        dst = src.replace('.def.in', '.def')
        patterns = [
            (r'^', 'LIBRARY {}\nEXPORTS '.format(src)),
            (r'^', '    ')]
    else:
        raise fbuild.ConfigFailed('unsupported platform: %s' % platform)

    return call('fbuild.builders.text.regex_substitute', ctx,
        dst, src, patterns)

# ------------------------------------------------------------------------------

def build_librustrt(ctx, config):
    """Compile the rust runtime library."""

    rustrt_def = def_substitute(ctx, config, 'src/rt/rustrt.def.in')

    # We need to use llc to compile the .ll objects.
    objs = config.llc.build_objects(Path.glob('src/rt/*.ll'),
        filetype='obj',
        arch='x86',
        relocation_model='pic')

    return config.cxx_shared.build_lib('rt/rustrt',
        srcs=Path.globall([
            'src/rt/*.cpp',
            'src/rt/arch/i386/*.{s,cpp}',
            'src/rt/isaac/*.cpp',
            'src/rt/sync/{timer,sync,lock_and_signal}.cpp',
            'src/rt/test/*.cpp']),
        objs=objs,
        includes=['src/rt/arch/i386', 'src/rt/isaac', 'src/rt/uthash'],
        external_libs=['pthread'],
        lflags=['-Wl,-exported_symbols_list,' + rustrt_def])

def build_main(ctx, config):
    """Compile the rust main.o object."""

    if 'windows' in config.platform:
        patterns = [(r'MAIN', r'WinMain@16')]
    else:
        patterns = [(r'MAIN', r'main')]

    main = config.llc.compile(
        call('fbuild.builders.text.regex_substitute', ctx,
            'src/rt/main.ll',
            'src/rt/main.ll.in',
            patterns),
        filetype='obj',
        arch='x86',
        relocation_model='pic')

    return main

# ------------------------------------------------------------------------------

def build_librustllvm(ctx, config):
    """Compile the rust llvm extensions."""

    cflags = config.llvm_config.cxxflags().split()
    lflags = config.llvm_config.ldflags().split() + \
             config.llvm_config.libs().split()

    rustllvmbits = config.cxx_static.build_lib('rustllvm/rustllvmbits',
        srcs=Path.glob('src/rustllvm/{MachOObjectFile,Passes,Passes2}.cpp'),
        cflags=cflags)

    rustllvm_def = def_substitute(ctx, config, 'src/rustllvm/rustllvm.def.in')

    return config.cxx_shared.build_lib('rustllvm/rustllvm',
        srcs=['src/rustllvm/RustWrapper.cpp'],
        objs=[rustllvmbits],
        cflags=cflags,
        lflags=lflags + ['-Wl,-exported_symbols_list,' + rustllvm_def])

# ------------------------------------------------------------------------------

@fbuild.db.caches
def fetch_rustc0(ctx):
    """Download the rustc bootstrap compiler."""

    (ctx.buildroot / 'dl').makedirs()
    (ctx.buildroot / 'stage0').makedirs()

    exe = Path('src/etc/get-snapshot.py')

    ctx.logger.log(' + ' + exe, color='yellow')
    ctx.execute(exe.relpath(ctx.buildroot),
        cwd=ctx.buildroot,
        env={'CFG_SRC_DIR': Path.getcwd().relpath(ctx.buildroot)})

    ctx.db.add_external_dependencies_to_call(
        srcs=['src/snapshots.txt'],
        dsts=Path.glob(ctx.buildroot / 'stage0/*'))

    return ctx.buildroot / 'stage0/rustc'

# ------------------------------------------------------------------------------

def build_compiler(ctx, config, libs):
    # Compile the intrinsic functions.
    dst = call('fbuild.builders.text.autoconf_config_file', ctx,
        'intrinsics/intrinsics.ll', 'src/rt/intrinsics/intrinsics.ll.in',
        {'CFG_LLVM_TRIPLE': config.llvm_config.host_target()})

    intrinsics = config.llvm_as(dst)

    # Compile the main object.
    main = build_main(ctx, config)

    # --------------------------------------------------------------------------
    # Compile the compiler a couple times.

    def make_rustc(rustc, stage_dir):
        # Copy the intrinsic functions into the stage directory.
        call('fbuild.builders.file.copy', ctx, intrinsics, stage_dir)

        return Rustc(ctx, rustc, config.cxx_shared,
            debug=ctx.options.debug,
            optimize=ctx.options.optimize,
            runtime_libpaths=[
                stage_dir,
                ctx.buildroot / 'rt',
                ctx.buildroot / 'rustllvm',
                config.llvm_config.libdir()])

    # Make the initial rustc.
    rustcs = [make_rustc(fetch_rustc0(ctx), ctx.buildroot / 'stage0')]

    # Now build all the compiler stages.
    for stage in range(1,4):
        rustc = rustcs[-1]
        stage_dir = ctx.buildroot / 'stage{}'.format(stage)
        stage_dir.makedirs()

        # Compile the standard library.
        libstd = rustc.link_lib(stage_dir / 'std',
            srcs=[
                rustc.compile('src/lib/std.rc', stage_dir / 'std',
                    libpaths=[stage_dir],
                    shared=True)],
            libs=libs)

        # Compile rustc.
        exe = rustc.link_exe('stage{}/rustc'.format(stage),
            srcs=[
                main,
                rustc.compile_glue(stage_dir / 'glue',
                    libpaths=[stage_dir]),
                rustc.compile('src/comp/rustc.rc', stage_dir / 'rustc',
                    libpaths=[stage_dir]),
                ],
            libs=libs + [libstd])

        rustcs.append(make_rustc(exe, stage_dir))

    # --------------------------------------------------------------------------
    # The last two compilers should be identical.

    ctx.logger.check('checking compiler fixpoint')
    with open(rustcs[-2].exe, 'rb') as f1:
        with open(rustcs[-1].exe, 'rb') as f2:
            if f1.read() == f2.read():
                ctx.logger.passed()
            else:
                ctx.logger.failed()

    # Return the last constructed rustc.
    return rustcs[-1]
