import * as path from "path";
import { ExtensionContext } from "vscode";
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
} from "vscode-languageclient/node";

export async function activate(ctx: ExtensionContext) {
    const debugServerPath = ctx.asAbsolutePath(
        path.join("..", "..", "target", "debug", "mixls")
    );

    const serverOptions: ServerOptions = {
        run: { command: debugServerPath },
        debug: { command: debugServerPath },
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: "file", language: "mixal" }],
        synchronize: {},
    };

    const client = new LanguageClient(
        "language-mixal",
        "language-mixal",
        serverOptions,
        clientOptions,
        true
    );

    await client.start();
}
